%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t35_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 33.83s
% Output     : Refutation 33.83s
% Verified   : 
% Statistics : Number of formulae       :  837 (2219 expanded)
%              Number of leaves         :  138 ( 895 expanded)
%              Depth                    :   32
%              Number of atoms          : 5786 (10912 expanded)
%              Number of equality atoms :  113 ( 592 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f205,f212,f219,f226,f249,f256,f263,f270,f277,f290,f312,f326,f350,f465,f564,f571,f585,f947,f958,f972,f1988,f1996,f2000,f2055,f2060,f2505,f2514,f2521,f2530,f2653,f2662,f2668,f2677,f2690,f2821,f2845,f2852,f2867,f2879,f2886,f2895,f2898,f2908,f2914,f3141,f3147,f5901,f5915,f6073,f6475,f6485,f6492,f6502,f6511,f6558,f6564,f6599,f6609,f9049,f9060,f10963,f10977,f11325,f11927,f11946,f12094,f12274,f12281,f21571,f21764,f21768,f21775,f21782,f21787,f21794,f21801,f21806,f21830,f22793,f22812,f23241,f23549,f23626,f23643,f23752,f23986,f23987,f25598,f25603,f25699,f25709,f26346,f26376])).

fof(f26376,plain,
    ( spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_870
    | spl7_971 ),
    inference(avatar_contradiction_clause,[],[f26375])).

fof(f26375,plain,
    ( $false
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_870
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26374,f5914])).

fof(f5914,plain,
    ( v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_458 ),
    inference(avatar_component_clause,[],[f5913])).

fof(f5913,plain,
    ( spl7_458
  <=> v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_458])])).

fof(f26374,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_870
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26373,f2805])).

fof(f2805,plain,
    ( v1_funct_1(u1_lattices(sK1))
    | ~ spl7_378 ),
    inference(avatar_component_clause,[],[f2804])).

fof(f2804,plain,
    ( spl7_378
  <=> v1_funct_1(u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_378])])).

fof(f26373,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_870
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26372,f6484])).

fof(f6484,plain,
    ( m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_466 ),
    inference(avatar_component_clause,[],[f6483])).

fof(f6483,plain,
    ( spl7_466
  <=> m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_466])])).

fof(f26372,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_870
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26371,f23237])).

fof(f23237,plain,
    ( r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_870 ),
    inference(avatar_component_clause,[],[f23236])).

fof(f23236,plain,
    ( spl7_870
  <=> r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_870])])).

fof(f26371,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_971 ),
    inference(superposition,[],[f26361,f21829])).

fof(f21829,plain,
    ( u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl7_856 ),
    inference(avatar_component_clause,[],[f21828])).

fof(f21828,plain,
    ( spl7_856
  <=> u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_856])])).

fof(f26361,plain,
    ( ! [X0] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26360,f2829])).

fof(f2829,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl7_384 ),
    inference(avatar_component_clause,[],[f2828])).

fof(f2828,plain,
    ( spl7_384
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_384])])).

fof(f26360,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26359,f10976])).

fof(f10976,plain,
    ( v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ spl7_564 ),
    inference(avatar_component_clause,[],[f10975])).

fof(f10975,plain,
    ( spl7_564
  <=> v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_564])])).

fof(f26359,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_971 ),
    inference(subsumption_resolution,[],[f26354,f12280])).

fof(f12280,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_590 ),
    inference(avatar_component_clause,[],[f12279])).

fof(f12279,plain,
    ( spl7_590
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_590])])).

fof(f26354,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_971 ),
    inference(resolution,[],[f25698,f21625])).

fof(f21625,plain,
    ( ! [X0,X1] :
        ( r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0)
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(X1)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21624,f2489])).

fof(f2489,plain,
    ( v1_funct_1(u2_lattices(sK1))
    | ~ spl7_366 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f2488,plain,
    ( spl7_366
  <=> v1_funct_1(u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_366])])).

fof(f21624,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21623,f2637])).

fof(f2637,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl7_372 ),
    inference(avatar_component_clause,[],[f2636])).

fof(f2636,plain,
    ( spl7_372
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_372])])).

fof(f21623,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21622,f10962])).

fof(f10962,plain,
    ( v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ spl7_560 ),
    inference(avatar_component_clause,[],[f10961])).

fof(f10961,plain,
    ( spl7_560
  <=> v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_560])])).

fof(f21622,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21621,f12273])).

fof(f12273,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_588 ),
    inference(avatar_component_clause,[],[f12272])).

fof(f12272,plain,
    ( spl7_588
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_588])])).

fof(f21621,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21620,f5900])).

fof(f5900,plain,
    ( v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_454 ),
    inference(avatar_component_clause,[],[f5899])).

fof(f5899,plain,
    ( spl7_454
  <=> v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_454])])).

fof(f21620,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21576,f6474])).

fof(f6474,plain,
    ( m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_464 ),
    inference(avatar_component_clause,[],[f6473])).

fof(f6473,plain,
    ( spl7_464
  <=> m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_464])])).

fof(f21576,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_2(X1,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X1)
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12211,f12462])).

fof(f12462,plain,
    ( u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))
    | ~ spl7_596 ),
    inference(avatar_component_clause,[],[f12461])).

fof(f12461,plain,
    ( spl7_596
  <=> u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_596])])).

fof(f12211,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_2(X71,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X69,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_1(X69)
        | ~ v1_funct_1(X71)
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12210,f6072])).

fof(f6072,plain,
    ( u1_struct_0(k7_filter_1(sK1,sK1)) = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_462 ),
    inference(avatar_component_clause,[],[f6071])).

fof(f6071,plain,
    ( spl7_462
  <=> u1_struct_0(k7_filter_1(sK1,sK1)) = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_462])])).

fof(f12210,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ v1_funct_2(X71,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X69,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_1(X69)
        | ~ v1_funct_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12209,f6072])).

fof(f12209,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X69,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_1(X69)
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12208,f6072])).

fof(f12208,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ v1_funct_2(X69,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_1(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12207,f6072])).

fof(f12207,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12206,f3548])).

fof(f3548,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK0)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_404 ),
    inference(avatar_component_clause,[],[f3547])).

fof(f3547,plain,
    ( spl7_404
  <=> u1_struct_0(k7_filter_1(sK0,sK0)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_404])])).

fof(f12206,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ v1_funct_2(X70,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12205,f3548])).

fof(f12205,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12204,f3548])).

fof(f12204,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ v1_funct_2(X68,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12203,f3548])).

fof(f12203,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12202,f325])).

fof(f325,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl7_27
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f12202,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12137,f311])).

fof(f311,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl7_23
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f12137,plain,
    ( ! [X70,X68,X71,X69] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X68,X69),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X70,X71))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_lattice2(u1_struct_0(sK0),X68,X70) )
    | ~ spl7_410 ),
    inference(superposition,[],[f128,f3568])).

fof(f3568,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_410 ),
    inference(avatar_component_clause,[],[f3567])).

fof(f3567,plain,
    ( spl7_410
  <=> u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_410])])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | r1_lattice2(X0,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t31_filter_1)).

fof(f25698,plain,
    ( ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ spl7_971 ),
    inference(avatar_component_clause,[],[f25697])).

fof(f25697,plain,
    ( spl7_971
  <=> ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_971])])).

fof(f26346,plain,
    ( spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866
    | spl7_969 ),
    inference(avatar_contradiction_clause,[],[f26345])).

fof(f26345,plain,
    ( $false
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26344,f6484])).

fof(f26344,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26343,f2805])).

fof(f26343,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26342,f5914])).

fof(f26342,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26341,f22778])).

fof(f22778,plain,
    ( r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_866 ),
    inference(avatar_component_clause,[],[f22777])).

fof(f22777,plain,
    ( spl7_866
  <=> r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_866])])).

fof(f26341,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_969 ),
    inference(superposition,[],[f26210,f21829])).

fof(f26210,plain,
    ( ! [X0] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1)))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26209,f2829])).

fof(f26209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0),u2_lattices(k7_filter_1(sK0,sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26208,f10976])).

fof(f26208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0),u2_lattices(k7_filter_1(sK0,sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_969 ),
    inference(subsumption_resolution,[],[f26207,f12280])).

fof(f26207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_1(X0)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X0),u2_lattices(k7_filter_1(sK0,sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_969 ),
    inference(resolution,[],[f21631,f25692])).

fof(f25692,plain,
    ( ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | ~ spl7_969 ),
    inference(avatar_component_clause,[],[f25691])).

fof(f25691,plain,
    ( spl7_969
  <=> ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_969])])).

fof(f21631,plain,
    ( ! [X2,X3] :
        ( r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(X3)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21630,f2489])).

fof(f21630,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21629,f2637])).

fof(f21629,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21628,f6474])).

fof(f21628,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21627,f10962])).

fof(f21627,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21626,f12273])).

fof(f21626,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21577,f5900])).

fof(f21577,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12211,f12462])).

fof(f25709,plain,
    ( spl7_44
    | spl7_23
    | spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(avatar_split_clause,[],[f25669,f24638,f21828,f12279,f10975,f6483,f6071,f5913,f3567,f3547,f2828,f2804,f324,f310,f448])).

fof(f448,plain,
    ( spl7_44
  <=> v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f24638,plain,
    ( spl7_930
  <=> v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_930])])).

fof(f25669,plain,
    ( v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(subsumption_resolution,[],[f22631,f24639])).

fof(f24639,plain,
    ( v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_930 ),
    inference(avatar_component_clause,[],[f24638])).

fof(f22631,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22630,f2805])).

fof(f22630,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22629,f2829])).

fof(f22629,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22628,f6484])).

fof(f22628,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22627,f10976])).

fof(f22627,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22626,f12280])).

fof(f22626,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22586,f5914])).

fof(f22586,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(superposition,[],[f12201,f21829])).

fof(f12201,plain,
    ( ! [X66,X67] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(X67,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X66,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_1(X67)
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12200,f6072])).

fof(f12200,plain,
    ( ! [X66,X67] :
        ( ~ v1_funct_2(X67,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X66,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_1(X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12199,f6072])).

fof(f12199,plain,
    ( ! [X66,X67] :
        ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X66,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12198,f3548])).

fof(f12198,plain,
    ( ! [X66,X67] :
        ( ~ v1_funct_2(X66,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X66)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12197,f3548])).

fof(f12197,plain,
    ( ! [X66,X67] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12196,f325])).

fof(f12196,plain,
    ( ! [X66,X67] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12136,f311])).

fof(f12136,plain,
    ( ! [X66,X67] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X66,X67),u1_struct_0(k7_filter_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_binop_1(X67,u1_struct_0(sK1)) )
    | ~ spl7_410 ),
    inference(superposition,[],[f126,f3568])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | v1_binop_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X3) )
                 => ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t23_filter_1)).

fof(f25699,plain,
    ( ~ spl7_969
    | ~ spl7_971
    | spl7_5
    | ~ spl7_6
    | spl7_21
    | spl7_23
    | spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_634
    | ~ spl7_648
    | ~ spl7_654
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(avatar_split_clause,[],[f25686,f24638,f21828,f13403,f13380,f13139,f12279,f10975,f6483,f6071,f5913,f3567,f3547,f2828,f2804,f324,f310,f288,f224,f217,f25697,f25691])).

fof(f217,plain,
    ( spl7_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f224,plain,
    ( spl7_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f288,plain,
    ( spl7_21
  <=> ~ v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f13139,plain,
    ( spl7_634
  <=> v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_634])])).

fof(f13380,plain,
    ( spl7_648
  <=> v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_648])])).

fof(f13403,plain,
    ( spl7_654
  <=> v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_654])])).

fof(f25686,plain,
    ( ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_634
    | ~ spl7_648
    | ~ spl7_654
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(subsumption_resolution,[],[f25685,f218])).

fof(f218,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f217])).

fof(f25685,plain,
    ( ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_634
    | ~ spl7_648
    | ~ spl7_654
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(subsumption_resolution,[],[f25684,f13140])).

fof(f13140,plain,
    ( v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_634 ),
    inference(avatar_component_clause,[],[f13139])).

fof(f25684,plain,
    ( ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_648
    | ~ spl7_654
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(subsumption_resolution,[],[f25683,f25670])).

fof(f25670,plain,
    ( v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_930 ),
    inference(subsumption_resolution,[],[f22625,f24639])).

fof(f22625,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22624,f2805])).

fof(f22624,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22623,f2829])).

fof(f22623,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22622,f6484])).

fof(f22622,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22621,f10976])).

fof(f22621,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22620,f12280])).

fof(f22620,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22585,f5914])).

fof(f22585,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(superposition,[],[f12195,f21829])).

fof(f12195,plain,
    ( ! [X64,X65] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(X65,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X64,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_1(X65)
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12194,f6072])).

fof(f12194,plain,
    ( ! [X64,X65] :
        ( ~ v1_funct_2(X65,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X64,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12193,f6072])).

fof(f12193,plain,
    ( ! [X64,X65] :
        ( ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X64,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12192,f3548])).

fof(f12192,plain,
    ( ! [X64,X65] :
        ( ~ v1_funct_2(X64,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12191,f3548])).

fof(f12191,plain,
    ( ! [X64,X65] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12190,f325])).

fof(f12190,plain,
    ( ! [X64,X65] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12135,f311])).

fof(f12135,plain,
    ( ! [X64,X65] :
        ( ~ v1_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X64,X65),u1_struct_0(k7_filter_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_binop_1(X64,u1_struct_0(sK0)) )
    | ~ spl7_410 ),
    inference(superposition,[],[f125,f3568])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | v1_binop_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f25683,plain,
    ( ~ v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_648
    | ~ spl7_654 ),
    inference(subsumption_resolution,[],[f25682,f13381])).

fof(f13381,plain,
    ( v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_648 ),
    inference(avatar_component_clause,[],[f13380])).

fof(f25682,plain,
    ( ~ v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_654 ),
    inference(subsumption_resolution,[],[f25681,f13404])).

fof(f13404,plain,
    ( v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_654 ),
    inference(avatar_component_clause,[],[f13403])).

fof(f25681,plain,
    ( ~ v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f25680,f225])).

fof(f225,plain,
    ( l3_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f224])).

fof(f25680,plain,
    ( ~ l3_lattices(sK0)
    | ~ v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_21 ),
    inference(resolution,[],[f289,f163])).

fof(f163,plain,(
    ! [X0] :
      ( v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( v10_lattices(X0)
      | ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( v10_lattices(X0)
      | ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
          & r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
          & v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
          & v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
          & v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
          & v1_binop_1(u2_lattices(X0),u1_struct_0(X0)) )
       => v10_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t17_lattice2)).

fof(f289,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f288])).

fof(f25603,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_967 ),
    inference(avatar_contradiction_clause,[],[f25602])).

fof(f25602,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_967 ),
    inference(subsumption_resolution,[],[f25601,f269])).

fof(f269,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_14
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f25601,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_967 ),
    inference(subsumption_resolution,[],[f25600,f255])).

fof(f255,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl7_10
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f25600,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_967 ),
    inference(subsumption_resolution,[],[f25599,f248])).

fof(f248,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl7_9
  <=> ~ v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f25599,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_967 ),
    inference(resolution,[],[f25597,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',cc1_lattices)).

fof(f25597,plain,
    ( ~ v6_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_967 ),
    inference(avatar_component_clause,[],[f25596])).

fof(f25596,plain,
    ( spl7_967
  <=> ~ v6_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_967])])).

fof(f25598,plain,
    ( ~ spl7_967
    | spl7_9
    | ~ spl7_894
    | spl7_931 ),
    inference(avatar_split_clause,[],[f24747,f24641,f23615,f247,f25596])).

fof(f23615,plain,
    ( spl7_894
  <=> l1_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_894])])).

fof(f24641,plain,
    ( spl7_931
  <=> ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_931])])).

fof(f24747,plain,
    ( ~ v6_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_894
    | ~ spl7_931 ),
    inference(subsumption_resolution,[],[f24746,f248])).

fof(f24746,plain,
    ( ~ v6_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_894
    | ~ spl7_931 ),
    inference(subsumption_resolution,[],[f24745,f23616])).

fof(f23616,plain,
    ( l1_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_894 ),
    inference(avatar_component_clause,[],[f23615])).

fof(f24745,plain,
    ( ~ v6_lattices(k7_filter_1(sK0,sK1))
    | ~ l1_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_931 ),
    inference(resolution,[],[f24642,f153])).

fof(f153,plain,(
    ! [X0] :
      ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',fc6_lattice2)).

fof(f24642,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_931 ),
    inference(avatar_component_clause,[],[f24641])).

fof(f23987,plain,
    ( spl7_634
    | spl7_23
    | spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_884 ),
    inference(avatar_split_clause,[],[f23754,f23578,f21828,f12279,f10975,f6483,f6071,f5913,f3567,f3547,f2828,f2804,f324,f310,f13139])).

fof(f23578,plain,
    ( spl7_884
  <=> v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_884])])).

fof(f23754,plain,
    ( v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_884 ),
    inference(subsumption_resolution,[],[f22613,f23579])).

fof(f23579,plain,
    ( v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_884 ),
    inference(avatar_component_clause,[],[f23578])).

fof(f22613,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22612,f2805])).

fof(f22612,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22611,f2829])).

fof(f22611,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22610,f6484])).

fof(f22610,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22609,f10976])).

fof(f22609,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22608,f12280])).

fof(f22608,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22583,f5914])).

fof(f22583,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(superposition,[],[f12183,f21829])).

fof(f12183,plain,
    ( ! [X61,X60] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(X61,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X60,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_1(X61)
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12182,f6072])).

fof(f12182,plain,
    ( ! [X61,X60] :
        ( ~ v1_funct_2(X61,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X60,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12181,f6072])).

fof(f12181,plain,
    ( ! [X61,X60] :
        ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X60,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12180,f3548])).

fof(f12180,plain,
    ( ! [X61,X60] :
        ( ~ v1_funct_2(X60,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12179,f3548])).

fof(f12179,plain,
    ( ! [X61,X60] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12178,f325])).

fof(f12178,plain,
    ( ! [X61,X60] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12133,f311])).

fof(f12133,plain,
    ( ! [X61,X60] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X60,X61),u1_struct_0(k7_filter_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v2_binop_1(X60,u1_struct_0(sK0)) )
    | ~ spl7_410 ),
    inference(superposition,[],[f122,f3568])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | v2_binop_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X3) )
                 => ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t24_filter_1)).

fof(f23986,plain,
    ( spl7_42
    | spl7_23
    | spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_884 ),
    inference(avatar_split_clause,[],[f23753,f23578,f21828,f12279,f10975,f6483,f6071,f5913,f3567,f3547,f2828,f2804,f324,f310,f442])).

fof(f442,plain,
    ( spl7_42
  <=> v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f23753,plain,
    ( v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856
    | ~ spl7_884 ),
    inference(subsumption_resolution,[],[f22619,f23579])).

fof(f22619,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22618,f2805])).

fof(f22618,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22617,f2829])).

fof(f22617,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22616,f6484])).

fof(f22616,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_564
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22615,f10976])).

fof(f22615,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_590
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22614,f12280])).

fof(f22614,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22584,f5914])).

fof(f22584,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_856 ),
    inference(superposition,[],[f12189,f21829])).

fof(f12189,plain,
    ( ! [X62,X63] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(X63,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X62,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_1(X63)
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12188,f6072])).

fof(f12188,plain,
    ( ! [X62,X63] :
        ( ~ v1_funct_2(X63,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X62,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12187,f6072])).

fof(f12187,plain,
    ( ! [X62,X63] :
        ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X62,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12186,f3548])).

fof(f12186,plain,
    ( ! [X62,X63] :
        ( ~ v1_funct_2(X62,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12185,f3548])).

fof(f12185,plain,
    ( ! [X62,X63] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12184,f325])).

fof(f12184,plain,
    ( ! [X62,X63] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12134,f311])).

fof(f12134,plain,
    ( ! [X62,X63] :
        ( ~ v2_binop_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X62,X63),u1_struct_0(k7_filter_1(sK0,sK1)))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v2_binop_1(X63,u1_struct_0(sK1)) )
    | ~ spl7_410 ),
    inference(superposition,[],[f123,f3568])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | v2_binop_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f23752,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_897 ),
    inference(avatar_contradiction_clause,[],[f23751])).

fof(f23751,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_897 ),
    inference(subsumption_resolution,[],[f23750,f269])).

fof(f23750,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_897 ),
    inference(subsumption_resolution,[],[f23749,f255])).

fof(f23749,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_897 ),
    inference(subsumption_resolution,[],[f23748,f248])).

fof(f23748,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_897 ),
    inference(resolution,[],[f23625,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f23625,plain,
    ( ~ v7_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_897 ),
    inference(avatar_component_clause,[],[f23624])).

fof(f23624,plain,
    ( spl7_897
  <=> ~ v7_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_897])])).

fof(f23643,plain,
    ( ~ spl7_14
    | spl7_895 ),
    inference(avatar_contradiction_clause,[],[f23642])).

fof(f23642,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_895 ),
    inference(subsumption_resolution,[],[f23641,f269])).

fof(f23641,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_895 ),
    inference(resolution,[],[f23619,f138])).

fof(f138,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_l3_lattices)).

fof(f23619,plain,
    ( ~ l1_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_895 ),
    inference(avatar_component_clause,[],[f23618])).

fof(f23618,plain,
    ( spl7_895
  <=> ~ l1_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_895])])).

fof(f23626,plain,
    ( ~ spl7_895
    | ~ spl7_897
    | spl7_9
    | spl7_885 ),
    inference(avatar_split_clause,[],[f23606,f23581,f247,f23624,f23618])).

fof(f23581,plain,
    ( spl7_885
  <=> ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_885])])).

fof(f23606,plain,
    ( ~ v7_lattices(k7_filter_1(sK0,sK1))
    | ~ l1_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_885 ),
    inference(subsumption_resolution,[],[f23605,f248])).

fof(f23605,plain,
    ( ~ v7_lattices(k7_filter_1(sK0,sK1))
    | ~ l1_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_885 ),
    inference(resolution,[],[f23582,f150])).

fof(f150,plain,(
    ! [X0] :
      ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v7_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',fc7_lattice2)).

fof(f23582,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_885 ),
    inference(avatar_component_clause,[],[f23581])).

fof(f23549,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_871 ),
    inference(avatar_contradiction_clause,[],[f23548])).

fof(f23548,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_871 ),
    inference(subsumption_resolution,[],[f23547,f248])).

fof(f23547,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_871 ),
    inference(subsumption_resolution,[],[f23546,f269])).

fof(f23546,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_871 ),
    inference(subsumption_resolution,[],[f23545,f255])).

fof(f23545,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_871 ),
    inference(resolution,[],[f23240,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t40_lattice2)).

fof(f23240,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_871 ),
    inference(avatar_component_clause,[],[f23239])).

fof(f23239,plain,
    ( spl7_871
  <=> ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_871])])).

fof(f23241,plain,
    ( ~ spl7_871
    | spl7_23
    | spl7_27
    | spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(avatar_split_clause,[],[f23014,f21828,f12461,f12279,f12272,f10975,f10961,f6483,f6473,f6071,f5913,f5899,f3567,f3547,f2828,f2804,f2636,f2488,f439,f324,f310,f23239])).

fof(f439,plain,
    ( spl7_41
  <=> ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f23014,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f23013,f12280])).

fof(f23013,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f23012,f2829])).

fof(f23012,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f23011,f10976])).

fof(f23011,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(superposition,[],[f22802,f21829])).

fof(f22802,plain,
    ( ! [X0] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,u1_lattices(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0)))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f22801,f2805])).

fof(f22801,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u1_lattices(sK1))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,u1_lattices(sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f22800,f6484])).

fof(f22800,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u1_lattices(sK1))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,u1_lattices(sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f22795,f5914])).

fof(f22795,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(u1_lattices(sK1))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,u1_lattices(sK1))) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_41
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(resolution,[],[f440,f21637])).

fof(f21637,plain,
    ( ! [X4,X5] :
        ( r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5)
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(X5)
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21636,f2489])).

fof(f21636,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21635,f2637])).

fof(f21635,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21634,f10962])).

fof(f21634,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21633,f12273])).

fof(f21633,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21632,f5900])).

fof(f21632,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21578,f6474])).

fof(f21578,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(X5,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ v1_funct_1(X5)
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12221,f12462])).

fof(f12221,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_2(X75,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X73,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_1(X75)
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12220,f6072])).

fof(f12220,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ v1_funct_2(X75,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X73,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_1(X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12219,f6072])).

fof(f12219,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X73,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12218,f6072])).

fof(f12218,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ v1_funct_2(X73,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_1(X73)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f12217,f6072])).

fof(f12217,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12216,f3548])).

fof(f12216,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ v1_funct_2(X74,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12215,f3548])).

fof(f12215,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12214,f3548])).

fof(f12214,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ v1_funct_2(X72,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410 ),
    inference(forward_demodulation,[],[f12213,f3548])).

fof(f12213,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12212,f325])).

fof(f12212,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_23
    | ~ spl7_410 ),
    inference(subsumption_resolution,[],[f12138,f311])).

fof(f12138,plain,
    ( ! [X74,X72,X75,X73] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X72,X73),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X74,X75))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_lattice2(u1_struct_0(sK1),X73,X75) )
    | ~ spl7_410 ),
    inference(superposition,[],[f129,f3568])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X0)
      | r1_lattice2(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f440,plain,
    ( ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f439])).

fof(f22812,plain,
    ( spl7_38
    | spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866 ),
    inference(avatar_split_clause,[],[f22794,f22777,f21828,f12461,f12279,f12272,f10975,f10961,f6483,f6473,f6071,f5913,f5899,f3567,f3547,f2828,f2804,f2636,f2488,f324,f310,f430])).

fof(f430,plain,
    ( spl7_38
  <=> r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f22794,plain,
    ( r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856
    | ~ spl7_866 ),
    inference(subsumption_resolution,[],[f22686,f22778])).

fof(f22686,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22685,f2805])).

fof(f22685,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_384
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22684,f2829])).

fof(f22684,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_564
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22683,f10976])).

fof(f22683,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_590
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22682,f12280])).

fof(f22682,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22681,f5914])).

fof(f22681,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_466
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(subsumption_resolution,[],[f22596,f6484])).

fof(f22596,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596
    | ~ spl7_856 ),
    inference(superposition,[],[f21643,f21829])).

fof(f21643,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(X7)
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21642,f2489])).

fof(f21642,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21641,f2637])).

fof(f21641,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21640,f6474])).

fof(f21640,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21639,f10962])).

fof(f21639,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21638,f12273])).

fof(f21638,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21579,f5900])).

fof(f21579,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(u2_lattices(sK1))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12221,f12462])).

fof(f22793,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_867 ),
    inference(avatar_contradiction_clause,[],[f22792])).

fof(f22792,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_867 ),
    inference(subsumption_resolution,[],[f22791,f248])).

fof(f22791,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_867 ),
    inference(subsumption_resolution,[],[f22790,f269])).

fof(f22790,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_867 ),
    inference(subsumption_resolution,[],[f22789,f255])).

fof(f22789,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_867 ),
    inference(resolution,[],[f22781,f161])).

fof(f161,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t41_lattice2)).

fof(f22781,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_867 ),
    inference(avatar_component_clause,[],[f22780])).

fof(f22780,plain,
    ( spl7_867
  <=> ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_867])])).

fof(f21830,plain,
    ( spl7_856
    | ~ spl7_104
    | ~ spl7_236 ),
    inference(avatar_split_clause,[],[f12577,f2058,f970,f21828])).

fof(f970,plain,
    ( spl7_104
  <=> k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f2058,plain,
    ( spl7_236
  <=> ! [X13,X12,X14] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X12,X13,X14)
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f12577,plain,
    ( u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl7_104
    | ~ spl7_236 ),
    inference(trivial_inequality_removal,[],[f12571])).

fof(f12571,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl7_104
    | ~ spl7_236 ),
    inference(superposition,[],[f2059,f971])).

fof(f971,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f970])).

fof(f2059,plain,
    ( ! [X14,X12,X13] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X12,X13,X14)
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)) = X14 )
    | ~ spl7_236 ),
    inference(avatar_component_clause,[],[f2058])).

fof(f21806,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_853 ),
    inference(avatar_contradiction_clause,[],[f21805])).

fof(f21805,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_853 ),
    inference(subsumption_resolution,[],[f21804,f269])).

fof(f21804,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_853 ),
    inference(subsumption_resolution,[],[f21803,f255])).

fof(f21803,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_853 ),
    inference(subsumption_resolution,[],[f21802,f248])).

fof(f21802,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_853 ),
    inference(resolution,[],[f21800,f141])).

fof(f141,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f21800,plain,
    ( ~ v4_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_853 ),
    inference(avatar_component_clause,[],[f21799])).

fof(f21799,plain,
    ( spl7_853
  <=> ~ v4_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_853])])).

fof(f21801,plain,
    ( ~ spl7_853
    | spl7_9
    | ~ spl7_30
    | spl7_851 ),
    inference(avatar_split_clause,[],[f21793,f21780,f348,f247,f21799])).

fof(f348,plain,
    ( spl7_30
  <=> l2_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f21780,plain,
    ( spl7_851
  <=> ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_851])])).

fof(f21793,plain,
    ( ~ v4_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_30
    | ~ spl7_851 ),
    inference(subsumption_resolution,[],[f21792,f248])).

fof(f21792,plain,
    ( ~ v4_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_30
    | ~ spl7_851 ),
    inference(subsumption_resolution,[],[f21791,f349])).

fof(f349,plain,
    ( l2_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f348])).

fof(f21791,plain,
    ( ~ v4_lattices(k7_filter_1(sK0,sK1))
    | ~ l2_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_851 ),
    inference(resolution,[],[f21781,f156])).

fof(f156,plain,(
    ! [X0] :
      ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',fc3_lattice2)).

fof(f21781,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_851 ),
    inference(avatar_component_clause,[],[f21780])).

fof(f21794,plain,
    ( spl7_48
    | ~ spl7_851
    | spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(avatar_split_clause,[],[f21619,f12461,f12272,f10961,f6473,f6071,f5899,f3567,f3547,f2636,f2488,f324,f310,f21780,f460])).

fof(f460,plain,
    ( spl7_48
  <=> v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f21619,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21618,f2489])).

fof(f21618,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21617,f2637])).

fof(f21617,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21616,f6474])).

fof(f21616,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21615,f10962])).

fof(f21615,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21614,f12273])).

fof(f21614,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21575,f5900])).

fof(f21575,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12201,f12462])).

fof(f21787,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | spl7_849 ),
    inference(avatar_contradiction_clause,[],[f21786])).

fof(f21786,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_849 ),
    inference(subsumption_resolution,[],[f21785,f269])).

fof(f21785,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_849 ),
    inference(subsumption_resolution,[],[f21784,f255])).

fof(f21784,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_849 ),
    inference(subsumption_resolution,[],[f21783,f248])).

fof(f21783,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_849 ),
    inference(resolution,[],[f21774,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f21774,plain,
    ( ~ v5_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_849 ),
    inference(avatar_component_clause,[],[f21773])).

fof(f21773,plain,
    ( spl7_849
  <=> ~ v5_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_849])])).

fof(f21782,plain,
    ( spl7_654
    | ~ spl7_851
    | spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(avatar_split_clause,[],[f21613,f12461,f12272,f10961,f6473,f6071,f5899,f3567,f3547,f2636,f2488,f324,f310,f21780,f13403])).

fof(f21613,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21612,f2489])).

fof(f21612,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21611,f2637])).

fof(f21611,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21610,f6474])).

fof(f21610,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21609,f10962])).

fof(f21609,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21608,f12273])).

fof(f21608,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21574,f5900])).

fof(f21574,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12195,f12462])).

fof(f21775,plain,
    ( ~ spl7_849
    | spl7_9
    | ~ spl7_30
    | spl7_847 ),
    inference(avatar_split_clause,[],[f21767,f21762,f348,f247,f21773])).

fof(f21762,plain,
    ( spl7_847
  <=> ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_847])])).

fof(f21767,plain,
    ( ~ v5_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_30
    | ~ spl7_847 ),
    inference(subsumption_resolution,[],[f21766,f248])).

fof(f21766,plain,
    ( ~ v5_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_30
    | ~ spl7_847 ),
    inference(subsumption_resolution,[],[f21765,f349])).

fof(f21765,plain,
    ( ~ v5_lattices(k7_filter_1(sK0,sK1))
    | ~ l2_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl7_847 ),
    inference(resolution,[],[f21763,f159])).

fof(f159,plain,(
    ! [X0] :
      ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',fc4_lattice2)).

fof(f21763,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ spl7_847 ),
    inference(avatar_component_clause,[],[f21762])).

fof(f21768,plain,
    ( spl7_46
    | ~ spl7_847
    | spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(avatar_split_clause,[],[f21607,f12461,f12272,f10961,f6473,f6071,f5899,f3567,f3547,f2636,f2488,f324,f310,f21762,f454])).

fof(f454,plain,
    ( spl7_46
  <=> v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f21607,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21606,f2489])).

fof(f21606,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21605,f2637])).

fof(f21605,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21604,f6474])).

fof(f21604,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21603,f10962])).

fof(f21603,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21602,f12273])).

fof(f21602,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21573,f5900])).

fof(f21573,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12189,f12462])).

fof(f21764,plain,
    ( spl7_648
    | ~ spl7_847
    | spl7_23
    | spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(avatar_split_clause,[],[f21601,f12461,f12272,f10961,f6473,f6071,f5899,f3567,f3547,f2636,f2488,f324,f310,f21762,f13380])).

fof(f21601,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21600,f2489])).

fof(f21600,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21599,f2637])).

fof(f21599,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21598,f6474])).

fof(f21598,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21597,f10962])).

fof(f21597,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_588
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21596,f12273])).

fof(f21596,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(subsumption_resolution,[],[f21572,f5900])).

fof(f21572,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_1(u2_lattices(sK1))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ spl7_23
    | ~ spl7_27
    | ~ spl7_404
    | ~ spl7_410
    | ~ spl7_462
    | ~ spl7_596 ),
    inference(superposition,[],[f12183,f12462])).

fof(f21571,plain,
    ( spl7_596
    | ~ spl7_104
    | ~ spl7_234 ),
    inference(avatar_split_clause,[],[f12368,f2053,f970,f12461])).

fof(f2053,plain,
    ( spl7_234
  <=> ! [X7,X8,X6] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X6,X7,X8)
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f12368,plain,
    ( u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))
    | ~ spl7_104
    | ~ spl7_234 ),
    inference(trivial_inequality_removal,[],[f12362])).

fof(f12362,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))
    | ~ spl7_104
    | ~ spl7_234 ),
    inference(superposition,[],[f2054,f971])).

fof(f2054,plain,
    ( ! [X6,X8,X7] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X6,X7,X8)
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)) = X7 )
    | ~ spl7_234 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f12281,plain,
    ( spl7_590
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_386 ),
    inference(avatar_split_clause,[],[f9164,f2834,f1994,f956,f12279])).

fof(f956,plain,
    ( spl7_100
  <=> k7_filter_1(sK0,sK0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK0)),u2_lattices(k7_filter_1(sK0,sK0)),u1_lattices(k7_filter_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f1994,plain,
    ( spl7_214
  <=> ! [X1,X0,X2] :
        ( k7_filter_1(sK0,sK0) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f2834,plain,
    ( spl7_386
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_386])])).

fof(f9164,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_386 ),
    inference(backward_demodulation,[],[f9114,f2835])).

fof(f2835,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl7_386 ),
    inference(avatar_component_clause,[],[f2834])).

fof(f9114,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK0)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_100
    | ~ spl7_214 ),
    inference(trivial_inequality_removal,[],[f9108])).

fof(f9108,plain,
    ( k7_filter_1(sK0,sK0) != k7_filter_1(sK0,sK0)
    | u1_struct_0(k7_filter_1(sK0,sK0)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_100
    | ~ spl7_214 ),
    inference(superposition,[],[f1995,f957])).

fof(f957,plain,
    ( k7_filter_1(sK0,sK0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK0)),u2_lattices(k7_filter_1(sK0,sK0)),u1_lattices(k7_filter_1(sK0,sK0)))
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f956])).

fof(f1995,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK0,sK0) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)) = X0 )
    | ~ spl7_214 ),
    inference(avatar_component_clause,[],[f1994])).

fof(f12274,plain,
    ( spl7_588
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_374 ),
    inference(avatar_split_clause,[],[f9138,f2642,f1994,f956,f12272])).

fof(f2642,plain,
    ( spl7_374
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_374])])).

fof(f9138,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_374 ),
    inference(backward_demodulation,[],[f9114,f2643])).

fof(f2643,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl7_374 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f12094,plain,
    ( spl7_410
    | ~ spl7_104
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f11963,f1998,f970,f3567])).

fof(f1998,plain,
    ( spl7_216
  <=> ! [X1,X0,X2] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f11963,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_104
    | ~ spl7_216 ),
    inference(trivial_inequality_removal,[],[f11958])).

fof(f11958,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_104
    | ~ spl7_216 ),
    inference(superposition,[],[f1999,f971])).

fof(f1999,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = X0 )
    | ~ spl7_216 ),
    inference(avatar_component_clause,[],[f1998])).

fof(f11946,plain,
    ( ~ spl7_100
    | spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560 ),
    inference(avatar_contradiction_clause,[],[f11945])).

fof(f11945,plain,
    ( $false
    | ~ spl7_100
    | ~ spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11944,f6474])).

fof(f11944,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11943,f6072])).

fof(f11943,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11942,f5900])).

fof(f11942,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11941,f6072])).

fof(f11941,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_193
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11940,f9138])).

fof(f11940,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_193
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11939,f3548])).

fof(f11939,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_193
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11938,f10962])).

fof(f11938,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_193
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404 ),
    inference(forward_demodulation,[],[f11937,f3548])).

fof(f11937,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_193
    | ~ spl7_366
    | ~ spl7_372 ),
    inference(subsumption_resolution,[],[f11936,f2637])).

fof(f11936,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_193
    | ~ spl7_366 ),
    inference(subsumption_resolution,[],[f11935,f2489])).

fof(f11935,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_193 ),
    inference(resolution,[],[f1905,f189])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_k6_filter_1)).

fof(f1905,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_193 ),
    inference(avatar_component_clause,[],[f1904])).

fof(f1904,plain,
    ( spl7_193
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).

fof(f11927,plain,
    ( ~ spl7_100
    | spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560 ),
    inference(avatar_contradiction_clause,[],[f11926])).

fof(f11926,plain,
    ( $false
    | ~ spl7_100
    | ~ spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_464
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11925,f6474])).

fof(f11925,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11924,f6072])).

fof(f11924,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_454
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11923,f5900])).

fof(f11923,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_462
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11922,f6072])).

fof(f11922,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_100
    | ~ spl7_191
    | ~ spl7_214
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11921,f9138])).

fof(f11921,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_191
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(forward_demodulation,[],[f11920,f3548])).

fof(f11920,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_191
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404
    | ~ spl7_560 ),
    inference(subsumption_resolution,[],[f11919,f10962])).

fof(f11919,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_191
    | ~ spl7_366
    | ~ spl7_372
    | ~ spl7_404 ),
    inference(forward_demodulation,[],[f11918,f3548])).

fof(f11918,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_191
    | ~ spl7_366
    | ~ spl7_372 ),
    inference(subsumption_resolution,[],[f11917,f2637])).

fof(f11917,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_191
    | ~ spl7_366 ),
    inference(subsumption_resolution,[],[f11913,f2489])).

fof(f11913,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_191 ),
    inference(resolution,[],[f1899,f190])).

fof(f190,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f1899,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ spl7_191 ),
    inference(avatar_component_clause,[],[f1898])).

fof(f1898,plain,
    ( spl7_191
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).

fof(f11325,plain,
    ( spl7_404
    | ~ spl7_100
    | ~ spl7_214 ),
    inference(avatar_split_clause,[],[f9114,f1994,f956,f3547])).

fof(f10977,plain,
    ( spl7_564
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_388 ),
    inference(avatar_split_clause,[],[f9165,f2840,f1994,f956,f10975])).

fof(f2840,plain,
    ( spl7_388
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_388])])).

fof(f9165,plain,
    ( v1_funct_2(u1_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_388 ),
    inference(backward_demodulation,[],[f9114,f2841])).

fof(f2841,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_388 ),
    inference(avatar_component_clause,[],[f2840])).

fof(f10963,plain,
    ( spl7_560
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_376 ),
    inference(avatar_split_clause,[],[f9139,f2648,f1994,f956,f10961])).

fof(f2648,plain,
    ( spl7_376
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_376])])).

fof(f9139,plain,
    ( v1_funct_2(u2_lattices(sK0),u1_struct_0(k7_filter_1(sK0,sK0)),u1_struct_0(sK0))
    | ~ spl7_100
    | ~ spl7_214
    | ~ spl7_376 ),
    inference(backward_demodulation,[],[f9114,f2649])).

fof(f2649,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_376 ),
    inference(avatar_component_clause,[],[f2648])).

fof(f9060,plain,
    ( spl7_177
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(avatar_contradiction_clause,[],[f9059])).

fof(f9059,plain,
    ( $false
    | ~ spl7_177
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9058,f2637])).

fof(f9058,plain,
    ( ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_177
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9057,f2643])).

fof(f9057,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_177
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9056,f2649])).

fof(f9056,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_177 ),
    inference(duplicate_literal_removal,[],[f9055])).

fof(f9055,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_177 ),
    inference(resolution,[],[f1852,f189])).

fof(f1852,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_177 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1851,plain,
    ( spl7_177
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).

fof(f9049,plain,
    ( spl7_175
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(avatar_contradiction_clause,[],[f9048])).

fof(f9048,plain,
    ( $false
    | ~ spl7_175
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9047,f2637])).

fof(f9047,plain,
    ( ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_175
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9046,f2643])).

fof(f9046,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_175
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f9045,f2649])).

fof(f9045,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_175 ),
    inference(duplicate_literal_removal,[],[f9041])).

fof(f9041,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_175 ),
    inference(resolution,[],[f1846,f190])).

fof(f1846,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_175 ),
    inference(avatar_component_clause,[],[f1845])).

fof(f1845,plain,
    ( spl7_175
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_175])])).

fof(f6609,plain,
    ( spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(avatar_contradiction_clause,[],[f6608])).

fof(f6608,plain,
    ( $false
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(subsumption_resolution,[],[f6607,f6484])).

fof(f6607,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6606,f6072])).

fof(f6606,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(subsumption_resolution,[],[f6605,f5914])).

fof(f6605,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6604,f6072])).

fof(f6604,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6603,f2829])).

fof(f6603,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_189
    | ~ spl7_378
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6602,f2805])).

fof(f6602,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_189
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6601,f2835])).

fof(f6601,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_189
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6600,f2841])).

fof(f6600,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_189 ),
    inference(resolution,[],[f1893,f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f1893,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl7_189 ),
    inference(avatar_component_clause,[],[f1892])).

fof(f1892,plain,
    ( spl7_189
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f6599,plain,
    ( spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(avatar_contradiction_clause,[],[f6598])).

fof(f6598,plain,
    ( $false
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(subsumption_resolution,[],[f6597,f6484])).

fof(f6597,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6596,f6072])).

fof(f6596,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(subsumption_resolution,[],[f6595,f5914])).

fof(f6595,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6594,f6072])).

fof(f6594,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6593,f2829])).

fof(f6593,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_187
    | ~ spl7_378
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6592,f2805])).

fof(f6592,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_187
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6591,f2835])).

fof(f6591,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_187
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6590,f2841])).

fof(f6590,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_187 ),
    inference(resolution,[],[f1887,f189])).

fof(f1887,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_187 ),
    inference(avatar_component_clause,[],[f1886])).

fof(f1886,plain,
    ( spl7_187
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).

fof(f6564,plain,
    ( spl7_173
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(avatar_contradiction_clause,[],[f6563])).

fof(f6563,plain,
    ( $false
    | ~ spl7_173
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6562,f2829])).

fof(f6562,plain,
    ( ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_173
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6561,f2835])).

fof(f6561,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_173
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6560,f2841])).

fof(f6560,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_173 ),
    inference(duplicate_literal_removal,[],[f6559])).

fof(f6559,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_173 ),
    inference(resolution,[],[f1840,f188])).

fof(f1840,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl7_173 ),
    inference(avatar_component_clause,[],[f1839])).

fof(f1839,plain,
    ( spl7_173
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f6558,plain,
    ( spl7_171
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(avatar_contradiction_clause,[],[f6557])).

fof(f6557,plain,
    ( $false
    | ~ spl7_171
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6556,f2829])).

fof(f6556,plain,
    ( ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_171
    | ~ spl7_386
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6555,f2835])).

fof(f6555,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_171
    | ~ spl7_388 ),
    inference(subsumption_resolution,[],[f6554,f2841])).

fof(f6554,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_171 ),
    inference(duplicate_literal_removal,[],[f6553])).

fof(f6553,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_171 ),
    inference(resolution,[],[f1834,f189])).

fof(f1834,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_171 ),
    inference(avatar_component_clause,[],[f1833])).

fof(f1833,plain,
    ( spl7_171
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f6511,plain,
    ( spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(avatar_contradiction_clause,[],[f6510])).

fof(f6510,plain,
    ( $false
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_388
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(subsumption_resolution,[],[f2841,f6509])).

fof(f6509,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_458
    | ~ spl7_462
    | ~ spl7_466 ),
    inference(subsumption_resolution,[],[f6508,f6484])).

fof(f6508,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6507,f6072])).

fof(f6507,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_458
    | ~ spl7_462 ),
    inference(subsumption_resolution,[],[f6506,f5914])).

fof(f6506,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386
    | ~ spl7_462 ),
    inference(forward_demodulation,[],[f6505,f6072])).

fof(f6505,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_384
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f6504,f2829])).

fof(f6504,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_185
    | ~ spl7_378
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f6503,f2805])).

fof(f6503,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_185
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2799,f2835])).

fof(f2799,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_185 ),
    inference(resolution,[],[f1881,f190])).

fof(f1881,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ spl7_185 ),
    inference(avatar_component_clause,[],[f1880])).

fof(f1880,plain,
    ( spl7_185
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).

fof(f6502,plain,
    ( spl7_389
    | ~ spl7_394 ),
    inference(avatar_contradiction_clause,[],[f6501])).

fof(f6501,plain,
    ( $false
    | ~ spl7_389
    | ~ spl7_394 ),
    inference(subsumption_resolution,[],[f6496,f2882])).

fof(f2882,plain,
    ( l1_lattices(sK0)
    | ~ spl7_394 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f2881,plain,
    ( spl7_394
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_394])])).

fof(f6496,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl7_389 ),
    inference(resolution,[],[f2844,f133])).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_u1_lattices)).

fof(f2844,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_389 ),
    inference(avatar_component_clause,[],[f2843])).

fof(f2843,plain,
    ( spl7_389
  <=> ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_389])])).

fof(f6492,plain,
    ( spl7_387
    | ~ spl7_394 ),
    inference(avatar_contradiction_clause,[],[f6491])).

fof(f6491,plain,
    ( $false
    | ~ spl7_387
    | ~ spl7_394 ),
    inference(subsumption_resolution,[],[f6487,f2882])).

fof(f6487,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl7_387 ),
    inference(resolution,[],[f2838,f134])).

fof(f134,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2838,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl7_387 ),
    inference(avatar_component_clause,[],[f2837])).

fof(f2837,plain,
    ( spl7_387
  <=> ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_387])])).

fof(f6485,plain,
    ( spl7_466
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_380 ),
    inference(avatar_split_clause,[],[f3255,f2810,f1986,f945,f6483])).

fof(f945,plain,
    ( spl7_98
  <=> k7_filter_1(sK1,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK1,sK1)),u2_lattices(k7_filter_1(sK1,sK1)),u1_lattices(k7_filter_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f1986,plain,
    ( spl7_212
  <=> ! [X1,X0,X2] :
        ( k7_filter_1(sK1,sK1) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f2810,plain,
    ( spl7_380
  <=> m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_380])])).

fof(f3255,plain,
    ( m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_380 ),
    inference(backward_demodulation,[],[f3199,f2811])).

fof(f2811,plain,
    ( m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_380 ),
    inference(avatar_component_clause,[],[f2810])).

fof(f3199,plain,
    ( u1_struct_0(k7_filter_1(sK1,sK1)) = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_98
    | ~ spl7_212 ),
    inference(trivial_inequality_removal,[],[f3191])).

fof(f3191,plain,
    ( k7_filter_1(sK1,sK1) != k7_filter_1(sK1,sK1)
    | u1_struct_0(k7_filter_1(sK1,sK1)) = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_98
    | ~ spl7_212 ),
    inference(superposition,[],[f1987,f946])).

fof(f946,plain,
    ( k7_filter_1(sK1,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK1,sK1)),u2_lattices(k7_filter_1(sK1,sK1)),u1_lattices(k7_filter_1(sK1,sK1)))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f945])).

fof(f1987,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK1,sK1) != g3_lattices(X0,X1,X2)
        | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = X0 )
    | ~ spl7_212 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f6475,plain,
    ( spl7_464
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_368 ),
    inference(avatar_split_clause,[],[f3222,f2494,f1986,f945,f6473])).

fof(f2494,plain,
    ( spl7_368
  <=> m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_368])])).

fof(f3222,plain,
    ( m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))))
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_368 ),
    inference(backward_demodulation,[],[f3199,f2495])).

fof(f2495,plain,
    ( m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_368 ),
    inference(avatar_component_clause,[],[f2494])).

fof(f6073,plain,
    ( spl7_462
    | ~ spl7_98
    | ~ spl7_212 ),
    inference(avatar_split_clause,[],[f3199,f1986,f945,f6071])).

fof(f5915,plain,
    ( spl7_458
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_382 ),
    inference(avatar_split_clause,[],[f3256,f2816,f1986,f945,f5913])).

fof(f2816,plain,
    ( spl7_382
  <=> v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_382])])).

fof(f3256,plain,
    ( v1_funct_2(u1_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_382 ),
    inference(backward_demodulation,[],[f3199,f2817])).

fof(f2817,plain,
    ( v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_382 ),
    inference(avatar_component_clause,[],[f2816])).

fof(f5901,plain,
    ( spl7_454
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_370 ),
    inference(avatar_split_clause,[],[f3223,f2500,f1986,f945,f5899])).

fof(f2500,plain,
    ( spl7_370
  <=> v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_370])])).

fof(f3223,plain,
    ( v1_funct_2(u2_lattices(sK1),u1_struct_0(k7_filter_1(sK1,sK1)),u1_struct_0(sK1))
    | ~ spl7_98
    | ~ spl7_212
    | ~ spl7_370 ),
    inference(backward_demodulation,[],[f3199,f2501])).

fof(f2501,plain,
    ( v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_370 ),
    inference(avatar_component_clause,[],[f2500])).

fof(f3147,plain,
    ( spl7_161
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(avatar_contradiction_clause,[],[f3146])).

fof(f3146,plain,
    ( $false
    | ~ spl7_161
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3145,f2489])).

fof(f3145,plain,
    ( ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_161
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3144,f2495])).

fof(f3144,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_161
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3143,f2501])).

fof(f3143,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_161 ),
    inference(duplicate_literal_removal,[],[f3142])).

fof(f3142,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_161 ),
    inference(resolution,[],[f1792,f189])).

fof(f1792,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_161 ),
    inference(avatar_component_clause,[],[f1791])).

fof(f1791,plain,
    ( spl7_161
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).

fof(f3141,plain,
    ( spl7_159
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(avatar_contradiction_clause,[],[f3140])).

fof(f3140,plain,
    ( $false
    | ~ spl7_159
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3139,f2489])).

fof(f3139,plain,
    ( ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_159
    | ~ spl7_368
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3138,f2495])).

fof(f3138,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_159
    | ~ spl7_370 ),
    inference(subsumption_resolution,[],[f3137,f2501])).

fof(f3137,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_159 ),
    inference(duplicate_literal_removal,[],[f3133])).

fof(f3133,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_159 ),
    inference(resolution,[],[f1786,f190])).

fof(f1786,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))
    | ~ spl7_159 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1785,plain,
    ( spl7_159
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).

fof(f2914,plain,
    ( spl7_157
    | ~ spl7_378
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(avatar_contradiction_clause,[],[f2913])).

fof(f2913,plain,
    ( $false
    | ~ spl7_157
    | ~ spl7_378
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2912,f2805])).

fof(f2912,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_157
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2911,f2811])).

fof(f2911,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_157
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2910,f2817])).

fof(f2910,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_157 ),
    inference(duplicate_literal_removal,[],[f2909])).

fof(f2909,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_157 ),
    inference(resolution,[],[f1780,f188])).

fof(f1780,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl7_157 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl7_157
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).

fof(f2908,plain,
    ( spl7_155
    | ~ spl7_378
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(avatar_contradiction_clause,[],[f2907])).

fof(f2907,plain,
    ( $false
    | ~ spl7_155
    | ~ spl7_378
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2906,f2805])).

fof(f2906,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_155
    | ~ spl7_380
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2905,f2811])).

fof(f2905,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_155
    | ~ spl7_382 ),
    inference(subsumption_resolution,[],[f2904,f2817])).

fof(f2904,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_155 ),
    inference(duplicate_literal_removal,[],[f2903])).

fof(f2903,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_155 ),
    inference(resolution,[],[f1774,f189])).

fof(f1774,plain,
    ( ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_155 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1773,plain,
    ( spl7_155
  <=> ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_155])])).

fof(f2898,plain,
    ( ~ spl7_6
    | spl7_395 ),
    inference(avatar_contradiction_clause,[],[f2897])).

fof(f2897,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_395 ),
    inference(subsumption_resolution,[],[f2896,f225])).

fof(f2896,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl7_395 ),
    inference(resolution,[],[f2885,f138])).

fof(f2885,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl7_395 ),
    inference(avatar_component_clause,[],[f2884])).

fof(f2884,plain,
    ( spl7_395
  <=> ~ l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_395])])).

fof(f2895,plain,
    ( spl7_383
    | ~ spl7_390 ),
    inference(avatar_contradiction_clause,[],[f2894])).

fof(f2894,plain,
    ( $false
    | ~ spl7_383
    | ~ spl7_390 ),
    inference(subsumption_resolution,[],[f2889,f2848])).

fof(f2848,plain,
    ( l1_lattices(sK1)
    | ~ spl7_390 ),
    inference(avatar_component_clause,[],[f2847])).

fof(f2847,plain,
    ( spl7_390
  <=> l1_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_390])])).

fof(f2889,plain,
    ( ~ l1_lattices(sK1)
    | ~ spl7_383 ),
    inference(resolution,[],[f2820,f133])).

fof(f2820,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_383 ),
    inference(avatar_component_clause,[],[f2819])).

fof(f2819,plain,
    ( spl7_383
  <=> ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_383])])).

fof(f2886,plain,
    ( ~ spl7_395
    | spl7_385 ),
    inference(avatar_split_clause,[],[f2855,f2831,f2884])).

fof(f2831,plain,
    ( spl7_385
  <=> ~ v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_385])])).

fof(f2855,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl7_385 ),
    inference(resolution,[],[f2832,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2832,plain,
    ( ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_385 ),
    inference(avatar_component_clause,[],[f2831])).

fof(f2879,plain,
    ( spl7_381
    | ~ spl7_390 ),
    inference(avatar_contradiction_clause,[],[f2878])).

fof(f2878,plain,
    ( $false
    | ~ spl7_381
    | ~ spl7_390 ),
    inference(subsumption_resolution,[],[f2874,f2848])).

fof(f2874,plain,
    ( ~ l1_lattices(sK1)
    | ~ spl7_381 ),
    inference(resolution,[],[f2814,f134])).

fof(f2814,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_381 ),
    inference(avatar_component_clause,[],[f2813])).

fof(f2813,plain,
    ( spl7_381
  <=> ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_381])])).

fof(f2867,plain,
    ( ~ spl7_2
    | spl7_391 ),
    inference(avatar_contradiction_clause,[],[f2866])).

fof(f2866,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_391 ),
    inference(subsumption_resolution,[],[f2865,f211])).

fof(f211,plain,
    ( l3_lattices(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_2
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f2865,plain,
    ( ~ l3_lattices(sK1)
    | ~ spl7_391 ),
    inference(resolution,[],[f2851,f138])).

fof(f2851,plain,
    ( ~ l1_lattices(sK1)
    | ~ spl7_391 ),
    inference(avatar_component_clause,[],[f2850])).

fof(f2850,plain,
    ( spl7_391
  <=> ~ l1_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_391])])).

fof(f2852,plain,
    ( ~ spl7_391
    | spl7_379 ),
    inference(avatar_split_clause,[],[f2824,f2807,f2850])).

fof(f2807,plain,
    ( spl7_379
  <=> ~ v1_funct_1(u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_379])])).

fof(f2824,plain,
    ( ~ l1_lattices(sK1)
    | ~ spl7_379 ),
    inference(resolution,[],[f2808,f132])).

fof(f2808,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_379 ),
    inference(avatar_component_clause,[],[f2807])).

fof(f2845,plain,
    ( ~ spl7_385
    | ~ spl7_387
    | ~ spl7_389
    | spl7_169 ),
    inference(avatar_split_clause,[],[f2699,f1827,f2843,f2837,f2831])).

fof(f1827,plain,
    ( spl7_169
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f2699,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_169 ),
    inference(duplicate_literal_removal,[],[f2695])).

fof(f2695,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ spl7_169 ),
    inference(resolution,[],[f1828,f190])).

fof(f1828,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_169 ),
    inference(avatar_component_clause,[],[f1827])).

fof(f2821,plain,
    ( ~ spl7_379
    | ~ spl7_381
    | ~ spl7_383
    | spl7_153 ),
    inference(avatar_split_clause,[],[f2535,f1767,f2819,f2813,f2807])).

fof(f1767,plain,
    ( spl7_153
  <=> ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f2535,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_153 ),
    inference(duplicate_literal_removal,[],[f2531])).

fof(f2531,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ spl7_153 ),
    inference(resolution,[],[f1768,f190])).

fof(f1768,plain,
    ( ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))
    | ~ spl7_153 ),
    inference(avatar_component_clause,[],[f1767])).

fof(f2690,plain,
    ( spl7_183
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(avatar_contradiction_clause,[],[f2689])).

fof(f2689,plain,
    ( $false
    | ~ spl7_183
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370
    | ~ spl7_372
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f2688,f2637])).

fof(f2688,plain,
    ( ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183
    | ~ spl7_366
    | ~ spl7_368
    | ~ spl7_370
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f2687,f2495])).

fof(f2687,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183
    | ~ spl7_366
    | ~ spl7_370
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f2686,f2501])).

fof(f2686,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183
    | ~ spl7_366
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f2685,f2489])).

fof(f2685,plain,
    ( ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183
    | ~ spl7_374
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f2684,f2643])).

fof(f2684,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183
    | ~ spl7_376 ),
    inference(subsumption_resolution,[],[f1913,f2649])).

fof(f1913,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_183 ),
    inference(resolution,[],[f1875,f188])).

fof(f1875,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)))
    | ~ spl7_183 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f1874,plain,
    ( spl7_183
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f2677,plain,
    ( ~ spl7_16
    | spl7_377 ),
    inference(avatar_contradiction_clause,[],[f2676])).

fof(f2676,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_377 ),
    inference(subsumption_resolution,[],[f2671,f276])).

fof(f276,plain,
    ( l2_lattices(sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl7_16
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f2671,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl7_377 ),
    inference(resolution,[],[f2652,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_u2_lattices)).

fof(f2652,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_377 ),
    inference(avatar_component_clause,[],[f2651])).

fof(f2651,plain,
    ( spl7_377
  <=> ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_377])])).

fof(f2668,plain,
    ( ~ spl7_16
    | spl7_375 ),
    inference(avatar_contradiction_clause,[],[f2667])).

fof(f2667,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_375 ),
    inference(subsumption_resolution,[],[f2663,f276])).

fof(f2663,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl7_375 ),
    inference(resolution,[],[f2646,f137])).

fof(f137,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2646,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl7_375 ),
    inference(avatar_component_clause,[],[f2645])).

fof(f2645,plain,
    ( spl7_375
  <=> ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_375])])).

fof(f2662,plain,
    ( ~ spl7_16
    | spl7_373 ),
    inference(avatar_contradiction_clause,[],[f2661])).

fof(f2661,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_373 ),
    inference(subsumption_resolution,[],[f2656,f276])).

fof(f2656,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl7_373 ),
    inference(resolution,[],[f2640,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2640,plain,
    ( ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_373 ),
    inference(avatar_component_clause,[],[f2639])).

fof(f2639,plain,
    ( spl7_373
  <=> ~ v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_373])])).

fof(f2653,plain,
    ( ~ spl7_373
    | ~ spl7_375
    | ~ spl7_377
    | spl7_167 ),
    inference(avatar_split_clause,[],[f1861,f1821,f2651,f2645,f2639])).

fof(f1821,plain,
    ( spl7_167
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f1861,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_167 ),
    inference(duplicate_literal_removal,[],[f1860])).

fof(f1860,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u2_lattices(sK0))
    | ~ spl7_167 ),
    inference(resolution,[],[f1822,f188])).

fof(f1822,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)))
    | ~ spl7_167 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f2530,plain,
    ( ~ spl7_12
    | spl7_371 ),
    inference(avatar_contradiction_clause,[],[f2529])).

fof(f2529,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_371 ),
    inference(subsumption_resolution,[],[f2524,f262])).

fof(f262,plain,
    ( l2_lattices(sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_12
  <=> l2_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f2524,plain,
    ( ~ l2_lattices(sK1)
    | ~ spl7_371 ),
    inference(resolution,[],[f2504,f136])).

fof(f2504,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_371 ),
    inference(avatar_component_clause,[],[f2503])).

fof(f2503,plain,
    ( spl7_371
  <=> ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_371])])).

fof(f2521,plain,
    ( ~ spl7_12
    | spl7_369 ),
    inference(avatar_contradiction_clause,[],[f2520])).

fof(f2520,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_369 ),
    inference(subsumption_resolution,[],[f2516,f262])).

fof(f2516,plain,
    ( ~ l2_lattices(sK1)
    | ~ spl7_369 ),
    inference(resolution,[],[f2498,f137])).

fof(f2498,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ spl7_369 ),
    inference(avatar_component_clause,[],[f2497])).

fof(f2497,plain,
    ( spl7_369
  <=> ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_369])])).

fof(f2514,plain,
    ( ~ spl7_12
    | spl7_367 ),
    inference(avatar_contradiction_clause,[],[f2513])).

fof(f2513,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_367 ),
    inference(subsumption_resolution,[],[f2508,f262])).

fof(f2508,plain,
    ( ~ l2_lattices(sK1)
    | ~ spl7_367 ),
    inference(resolution,[],[f2492,f135])).

fof(f2492,plain,
    ( ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_367 ),
    inference(avatar_component_clause,[],[f2491])).

fof(f2491,plain,
    ( spl7_367
  <=> ~ v1_funct_1(u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_367])])).

fof(f2505,plain,
    ( ~ spl7_367
    | ~ spl7_369
    | ~ spl7_371
    | spl7_151 ),
    inference(avatar_split_clause,[],[f1801,f1761,f2503,f2497,f2491])).

fof(f1761,plain,
    ( spl7_151
  <=> ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

fof(f1801,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_151 ),
    inference(duplicate_literal_removal,[],[f1800])).

fof(f1800,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ spl7_151 ),
    inference(resolution,[],[f1762,f188])).

fof(f1762,plain,
    ( ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)))
    | ~ spl7_151 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f2060,plain,
    ( ~ spl7_183
    | ~ spl7_185
    | ~ spl7_187
    | ~ spl7_189
    | ~ spl7_191
    | ~ spl7_193
    | spl7_236
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f631,f583,f2058,f1904,f1898,f1892,f1886,f1880,f1874])).

fof(f583,plain,
    ( spl7_64
  <=> k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f631,plain,
    ( ! [X14,X12,X13] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X12,X13,X14)
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)))
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)) = X14 )
    | ~ spl7_64 ),
    inference(superposition,[],[f184,f584])).

fof(f584,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f583])).

fof(f184,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X1)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ! [X3,X4,X5] :
          ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ! [X3,X4,X5] :
          ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X3,X4,X5] :
          ( g3_lattices(X0,X1,X2) = g3_lattices(X3,X4,X5)
         => ( X2 = X5
            & X1 = X4
            & X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',free_g3_lattices)).

fof(f2055,plain,
    ( ~ spl7_183
    | ~ spl7_185
    | ~ spl7_187
    | ~ spl7_189
    | ~ spl7_191
    | ~ spl7_193
    | spl7_234
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f629,f583,f2053,f1904,f1898,f1892,f1886,f1880,f1874])).

fof(f629,plain,
    ( ! [X6,X8,X7] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X6,X7,X8)
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)))
        | k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)) = X7 )
    | ~ spl7_64 ),
    inference(superposition,[],[f183,f584])).

fof(f183,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X1)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f2000,plain,
    ( ~ spl7_183
    | ~ spl7_185
    | ~ spl7_187
    | ~ spl7_189
    | ~ spl7_191
    | ~ spl7_193
    | spl7_216
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f627,f583,f1998,f1904,f1898,f1892,f1886,f1880,f1874])).

fof(f627,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X0,X1,X2)
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)))
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = X0 )
    | ~ spl7_64 ),
    inference(superposition,[],[f182,f584])).

fof(f182,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f1996,plain,
    ( ~ spl7_167
    | ~ spl7_169
    | ~ spl7_171
    | ~ spl7_173
    | ~ spl7_175
    | ~ spl7_177
    | spl7_214
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f617,f569,f1994,f1851,f1845,f1839,f1833,f1827,f1821])).

fof(f569,plain,
    ( spl7_60
  <=> k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f617,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK0,sK0) != g3_lattices(X0,X1,X2)
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)))
        | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)) = X0 )
    | ~ spl7_60 ),
    inference(superposition,[],[f182,f570])).

fof(f570,plain,
    ( k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f569])).

fof(f1988,plain,
    ( ~ spl7_151
    | ~ spl7_153
    | ~ spl7_155
    | ~ spl7_157
    | ~ spl7_159
    | ~ spl7_161
    | spl7_212
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f606,f562,f1986,f1791,f1785,f1779,f1773,f1767,f1761])).

fof(f562,plain,
    ( spl7_58
  <=> k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f606,plain,
    ( ! [X2,X0,X1] :
        ( k7_filter_1(sK1,sK1) != g3_lattices(X0,X1,X2)
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
        | ~ v1_funct_2(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | ~ m1_subset_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))
        | ~ v1_funct_1(k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)))
        | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = X0 )
    | ~ spl7_58 ),
    inference(superposition,[],[f182,f563])).

fof(f563,plain,
    ( k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f562])).

fof(f972,plain,
    ( spl7_104
    | spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f546,f224,f217,f210,f203,f970])).

fof(f203,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f546,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f542,f211])).

fof(f542,plain,
    ( ~ l3_lattices(sK1)
    | k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f389,f204])).

fof(f204,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f203])).

fof(f389,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | k7_filter_1(sK0,X0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,X0)),u2_lattices(k7_filter_1(sK0,X0)),u1_lattices(k7_filter_1(sK0,X0))) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f388,f241])).

fof(f241,plain,
    ( ! [X1] :
        ( l3_lattices(k7_filter_1(sK0,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f237,f218])).

fof(f237,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ l3_lattices(X1)
        | l3_lattices(k7_filter_1(sK0,X1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f225,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_k7_filter_1)).

fof(f388,plain,
    ( ! [X0] :
        ( ~ l3_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(k7_filter_1(sK0,X0))
        | k7_filter_1(sK0,X0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,X0)),u2_lattices(k7_filter_1(sK0,X0)),u1_lattices(k7_filter_1(sK0,X0))) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f240,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v3_lattices(X0)
      | ~ l3_lattices(X0)
      | g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0
      | ~ v3_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0
      | ~ v3_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( v3_lattices(X0)
       => g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',abstractness_v3_lattices)).

fof(f240,plain,
    ( ! [X0] :
        ( v3_lattices(k7_filter_1(sK0,X0))
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f236,f218])).

fof(f236,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | v3_lattices(k7_filter_1(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f225,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | v3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f958,plain,
    ( spl7_100
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f545,f224,f217,f956])).

fof(f545,plain,
    ( k7_filter_1(sK0,sK0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK0)),u2_lattices(k7_filter_1(sK0,sK0)),u1_lattices(k7_filter_1(sK0,sK0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f541,f225])).

fof(f541,plain,
    ( ~ l3_lattices(sK0)
    | k7_filter_1(sK0,sK0) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK0)),u2_lattices(k7_filter_1(sK0,sK0)),u1_lattices(k7_filter_1(sK0,sK0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f389,f218])).

fof(f947,plain,
    ( spl7_98
    | spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f538,f210,f203,f945])).

fof(f538,plain,
    ( k7_filter_1(sK1,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK1,sK1)),u2_lattices(k7_filter_1(sK1,sK1)),u1_lattices(k7_filter_1(sK1,sK1)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f534,f211])).

fof(f534,plain,
    ( ~ l3_lattices(sK1)
    | k7_filter_1(sK1,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK1,sK1)),u2_lattices(k7_filter_1(sK1,sK1)),u1_lattices(k7_filter_1(sK1,sK1)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f378,f204])).

fof(f378,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | k7_filter_1(sK1,X0) = g3_lattices(u1_struct_0(k7_filter_1(sK1,X0)),u2_lattices(k7_filter_1(sK1,X0)),u1_lattices(k7_filter_1(sK1,X0))) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f377,f233])).

fof(f233,plain,
    ( ! [X1] :
        ( l3_lattices(k7_filter_1(sK1,X1))
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f229,f204])).

fof(f229,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X1)
        | l3_lattices(k7_filter_1(sK1,X1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f211,f171])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ l3_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(k7_filter_1(sK1,X0))
        | k7_filter_1(sK1,X0) = g3_lattices(u1_struct_0(k7_filter_1(sK1,X0)),u2_lattices(k7_filter_1(sK1,X0)),u1_lattices(k7_filter_1(sK1,X0))) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f232,f140])).

fof(f232,plain,
    ( ! [X0] :
        ( v3_lattices(k7_filter_1(sK1,X0))
        | ~ l3_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f228,f204])).

fof(f228,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | v3_lattices(k7_filter_1(sK1,X0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f211,f170])).

fof(f585,plain,
    ( spl7_64
    | spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f425,f224,f217,f210,f203,f583])).

fof(f425,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f421,f211])).

fof(f421,plain,
    ( ~ l3_lattices(sK1)
    | k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f242,f204])).

fof(f242,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ l3_lattices(X2)
        | k7_filter_1(sK0,X2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(X2),u2_lattices(sK0),u2_lattices(X2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(X2),u1_lattices(sK0),u1_lattices(X2))) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f238,f218])).

fof(f238,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X2)
        | ~ l3_lattices(X2)
        | k7_filter_1(sK0,X2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(X2),u2_lattices(sK0),u2_lattices(X2)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(X2),u1_lattices(sK0),u1_lattices(X2))) )
    | ~ spl7_6 ),
    inference(resolution,[],[f225,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1))) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',d7_filter_1)).

fof(f571,plain,
    ( spl7_60
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f424,f224,f217,f569])).

fof(f424,plain,
    ( k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f420,f225])).

fof(f420,plain,
    ( ~ l3_lattices(sK0)
    | k7_filter_1(sK0,sK0) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u2_lattices(sK0),u2_lattices(sK0)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_lattices(sK0),u1_lattices(sK0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f242,f218])).

fof(f564,plain,
    ( spl7_58
    | spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f417,f210,f203,f562])).

fof(f417,plain,
    ( k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f413,f211])).

fof(f413,plain,
    ( ~ l3_lattices(sK1)
    | k7_filter_1(sK1,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u2_lattices(sK1),u2_lattices(sK1)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_lattices(sK1),u1_lattices(sK1)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f234,f204])).

fof(f234,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ l3_lattices(X2)
        | k7_filter_1(sK1,X2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(X2),u2_lattices(sK1),u2_lattices(X2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(X2),u1_lattices(sK1),u1_lattices(X2))) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f230,f204])).

fof(f230,plain,
    ( ! [X2] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X2)
        | ~ l3_lattices(X2)
        | k7_filter_1(sK1,X2) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(X2),u2_lattices(sK1),u2_lattices(X2)),k6_filter_1(u1_struct_0(sK1),u1_struct_0(X2),u1_lattices(sK1),u1_lattices(X2))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f211,f164])).

fof(f465,plain,
    ( ~ spl7_39
    | ~ spl7_41
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_47
    | ~ spl7_49
    | spl7_1
    | ~ spl7_2
    | spl7_19 ),
    inference(avatar_split_clause,[],[f293,f282,f210,f203,f463,f457,f451,f445,f439,f433])).

fof(f433,plain,
    ( spl7_39
  <=> ~ r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f445,plain,
    ( spl7_43
  <=> ~ v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f451,plain,
    ( spl7_45
  <=> ~ v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f457,plain,
    ( spl7_47
  <=> ~ v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f463,plain,
    ( spl7_49
  <=> ~ v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f282,plain,
    ( spl7_19
  <=> ~ v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f293,plain,
    ( ~ v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f292,f204])).

fof(f292,plain,
    ( ~ v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | v2_struct_0(sK1)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f291,f211])).

fof(f291,plain,
    ( ~ l3_lattices(sK1)
    | ~ v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | ~ r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | v2_struct_0(sK1)
    | ~ spl7_19 ),
    inference(resolution,[],[f283,f163])).

fof(f283,plain,
    ( ~ v10_lattices(sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f282])).

fof(f350,plain,
    ( spl7_30
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f300,f268,f348])).

fof(f300,plain,
    ( l2_lattices(k7_filter_1(sK0,sK1))
    | ~ spl7_14 ),
    inference(resolution,[],[f269,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f326,plain,
    ( ~ spl7_27
    | spl7_5
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f305,f275,f217,f324])).

fof(f305,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f235,f304])).

fof(f304,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f276,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',dt_l2_lattices)).

fof(f235,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(resolution,[],[f218,f162])).

fof(f162,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',fc2_struct_0)).

fof(f312,plain,
    ( ~ spl7_23
    | spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f296,f261,f203,f310])).

fof(f296,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f227,f295])).

fof(f295,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f262,f130])).

fof(f227,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f204,f162])).

fof(f290,plain,
    ( ~ spl7_19
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f198,f288,f282])).

fof(f198,plain,
    ( ~ v10_lattices(sK0)
    | ~ v10_lattices(sK1) ),
    inference(subsumption_resolution,[],[f197,f114])).

fof(f114,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & l3_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1))
          & l3_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & l3_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1))
          & l3_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
             => ( l3_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
           => ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t35_filter_1.p',t35_filter_1)).

fof(f197,plain,
    ( ~ v10_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f196,f113])).

fof(f113,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f196,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f195,f119])).

fof(f119,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f195,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f112,f118])).

fof(f118,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f277,plain,
    ( spl7_16
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f239,f224,f275])).

fof(f239,plain,
    ( l2_lattices(sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f225,f139])).

fof(f270,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f117,f268])).

fof(f117,plain,(
    l3_lattices(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f263,plain,
    ( spl7_12
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f231,f210,f261])).

fof(f231,plain,
    ( l2_lattices(sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f211,f139])).

fof(f256,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f116,f254])).

fof(f116,plain,(
    v10_lattices(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f249,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f115,f247])).

fof(f115,plain,(
    ~ v2_struct_0(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f226,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f119,f224])).

fof(f219,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f118,f217])).

fof(f212,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f114,f210])).

fof(f205,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f113,f203])).
%------------------------------------------------------------------------------
