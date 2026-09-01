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
  main_result&.dig("declaration") == "TopologicalComputationalPathsFollowup.topological_smith_exactness"
unless followup
  source = sources.first
  abort "the source must be adapted" unless source["relationship"] == "adapts"
  abort "the source must be pinned to a full commit" unless source["id"].to_s.match?(%r{/\b[0-9a-f]{40}\b/})
  abort "the source must identify the topological manuscript" unless source["id"].to_s.end_with?("/paper/topological/main.tex")
end
expected_declaration = followup ? "TopologicalComputationalPathsFollowup.topological_smith_exactness" : "TopologicalComputationalPaths.main_result"
expected_file = followup ? "FollowupSolution.lean" : "Solution.lean"
expected_comparator = followup ? "comparator-followup.json" : "comparator.json"
  abort "status.main_results must identify the follow-up declaration" unless main_result.is_a?(Hash) &&
  main_result["declaration"] == expected_declaration &&
  main_result["file"] == expected_file &&
  main_result["sorry_count"] == 0 &&
  main_result["axioms"] == expected_axioms &&
  main_result["comparator_config"] == expected_comparator

if followup
  msc = document.dig("classification", "msc2020")
  abort "follow-up metadata must not classify the result as 68V20" if msc.include?("68V20")

  interest = document.fetch("research_interest")
  abort "follow-up metadata must describe research interest" unless interest.is_a?(Hash)
  contribution = interest["selected_contribution"].to_s
  abort "research-interest statement must identify the selected quotient-topology and Smith theorem" unless
    contribution.include?("topological_smith_exactness") &&
      contribution.include?("monodromy-stabilizer") &&
      contribution.include?("product")
  abort "research-interest statement must explain paper-worthiness" unless
    interest["paper_worthiness"].to_s.strip.length >= 80

  fields = main_result.fetch("selected_fields")
  expected_fields = [
    "TopologicalSmithExactnessCertificate.covering_map_image_is_monodromy_stabilizer",
    "TopologicalSmithExactnessCertificate.quotient_product_hypothesis_sharp",
    "TopologicalSmithExactnessCertificate.rectangular_cokernel_short_exact",
    "TopologicalSmithExactnessCertificate.winding_matrix_compatibility",
    "FiniteTorusWindingMatrixCompatibility.matrix_map_smith_image_iff",
    "FiniteTorusWindingMatrixCompatibility.computational_path_winding_bridge",
    "TopologicalSmithExactnessCertificate.matrix_composition",
    "TopologicalSmithExactnessCertificate.rectangular_composition_profile",
    "TopologicalSmithExactnessCertificate.smith_cokernel_profile",
    "TopologicalSmithExactnessCertificate.determinant_index",
    "TopologicalSmithExactnessCertificate.prime_power_torsion_profile"
  ]
  abort "selected fields must match the selected quotient-topology and Smith theorem" unless fields == expected_fields
  # Validate against the statement-facing structure, not merely a token that
  # happens to occur somewhere in the proof file.  This keeps metadata scope
  # tied to fields the Comparator actually asks the Challenge to expose.
  selected_source = File.binread("FollowupChallenge.lean")
  fields.each do |field|
    leaf = field.split(".").last
    abort "selected field is not declared in FollowupChallenge.lean: #{field}" unless
      selected_source.match?(/^\s+#{Regexp.escape(leaf)}\s*:/)
  end

  original_sources = sources.select { |source| source["type"] == "original-proof" }
  abort "follow-up must declare exactly one original-proof source" unless original_sources.length == 1
  original_source = original_sources.first
  abort "original-proof source must identify the selected Topological Smith theorem" unless
    original_source["title"].to_s.include?("Topological Smith exactness") &&
      original_source["relationship"] == "other"
  local_sources = sources.select { |source| source["type"] == "formalization" }
  abort "follow-up must not cite its local Lean development as a source" unless local_sources.empty?
  invalid_relationships = sources.reject do |source|
    %w[background other].include?(source["relationship"])
  end
  abort "original-proof follow-up sources must be background or other" unless invalid_relationships.empty?
end

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
