# IGPL length and figure guidance

Checked 8 October 2026 against official publisher sources.

The [Logic Journal of the IGPL instructions](https://academic.oup.com/jigpal/pages/General_Instructions)
ask authors to restrict papers to **about 30 printed pages**. This is approximate
wording; the page does not state a hard maximum, numerical figure limit, word
limit or references exemption. The user's 35-page working target is distinct.
Our 35-page count includes references and visible review-copy alt text, using
the repository's existing 10-point amsart layout. It is not a verified count in
IGPL's eventual production layout, and acceptance or format approval is not implied.

The same journal page requires legible figure lettering after reduction and
alt-text descriptions directly under figure legends in the main manuscript.
All eleven main figures have authored alt text beneath their captions. These
are vector TikZ diagrams with the existing small-text size retained; no figure
was reduced merely to meet the page target. The publisher says alt text is
omitted from the eventual typeset article; it is visible in this review copy.
No page or colour charges are stated by the journal page.

No journal-specific mandatory LaTeX class or supplement policy was verified.
General OUP guidance recommends a journal template where available and
`article.cls` otherwise, with supporting sources. This working manuscript still
uses its existing `amsart` class; a future submission package should reconcile
that general advice and IGPL's manuscript-format instructions. Neither this
page count nor the present class establishes production-format compliance.
[General OUP manuscript guidance](https://academic.oup.com/pages/for-authors/journals/preparing-and-submitting-your-manuscript)
treats supplements as complementary material cited from the main article,
not material needed to understand it. The explanatory figures therefore remain
in the main paper. The supplement retains longer calculations, complete
verification maps and historical artifact boundaries. Existing amsart typography
and margins are preserved, rather than claiming an unverified IGPL template.

This revision updates the existing draft PR only. No journal contact, submission,
registry action or merge was performed.
