#!/usr/bin/env ruby
# frozen_string_literal: true

require "yaml"

path = ARGV.fetch(0, "formalization.yaml")
document = YAML.safe_load(File.binread(path), aliases: false)
abort "#{path} must contain one top-level mapping" unless document.is_a?(Hash)
abort "#{path} must declare version v0.4" unless document["version"] == "v0.4"

%w[project sources automation review].each do |section|
  abort "#{path} is missing required section #{section}" unless document[section].is_a?(Hash) ||
    (section == "sources" && document[section].is_a?(Array))
end

project = document.fetch("project")
abort "project.name must be nonempty" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "project.description must be nonempty" unless project["description"].is_a?(String) && !project["description"].strip.empty?
abort "project.authors must be nonempty" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "project.responsible_maintainers must be nonempty" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "project.license must be MIT" unless project["license"] == "MIT"

repository = document.fetch("repository")
abort "repository.role must be substantive-development" unless repository["role"] == "substantive-development"

arxiv = document.dig("classification", "arxiv")
abort "classification.arxiv must contain one or two categories" unless arxiv.is_a?(Array) && arxiv.length.between?(1, 2)

sources = document.fetch("sources")
abort "sources must be nonempty" unless sources.is_a?(Array) && !sources.empty?

status = document.fetch("status")
abort "status.sorry_count must be zero" unless status["sorry_count"] == 0
abort "status.sorry_in_definitions must be zero" unless status["sorry_in_definitions"] == 0
expected_axioms = ["propext", "Classical.choice", "Quot.sound"]
abort "status.axioms must list the three standard proof axioms" unless status["axioms"] == expected_axioms
main_result = status.dig("main_results", 0)
followup = File.basename(path) == "formalization-followup.yaml" ||
  main_result&.dig("declaration") == "TopologicalComputationalPathsFollowup.main_result"
unless followup
  source = sources.first
  abort "the source must be adapted" unless source["relationship"] == "adapts"
  abort "the source must be pinned to a full commit" unless source["id"].to_s.match?(%r{/\b[0-9a-f]{40}\b/})
  abort "the source must identify the topological manuscript" unless source["id"].to_s.end_with?("/paper/topological/main.tex")
end
expected_declaration = followup ? "TopologicalComputationalPathsFollowup.main_result" : "TopologicalComputationalPaths.main_result"
expected_file = followup ? "FollowupSolution.lean" : "Solution.lean"
expected_comparator = followup ? "comparator-followup.json" : "comparator.json"
abort "status.main_results must identify main_result" unless main_result.is_a?(Hash) &&
  main_result["declaration"] == expected_declaration &&
  main_result["file"] == expected_file &&
  main_result["sorry_count"] == 0 &&
  main_result["axioms"] == expected_axioms &&
  main_result["comparator_config"] == expected_comparator

methods = document.dig("automation", "methods")
method_names = methods.is_a?(Array) ? methods.map { |entry| entry["method"] } : []
abort "automation.methods must record manual and agent work" unless method_names.include?("manual") && method_names.include?("agent")

review = document.fetch("review")
abort "review.status must remain self-assessed until external review" unless review["status"] == "self-assessed"
abort "reviewers must be an empty array when there are no reviewers" unless review["reviewers"] == []

placeholders = []
walker = lambda do |value, location|
  case value
  when Hash
    value.each { |key, child| walker.call(child, "#{location}.#{key}") }
  when Array
    value.each_with_index { |child, index| walker.call(child, "#{location}[#{index}]") }
  when String
    placeholders << location if value.lstrip.start_with?("TEMPLATE", "TEMPLATE:")
  end
end
walker.call(document, "$")
abort "formalization metadata contains TEMPLATE placeholders: #{placeholders.join(', ')}" unless placeholders.empty?

puts "#{path} validation passed"
