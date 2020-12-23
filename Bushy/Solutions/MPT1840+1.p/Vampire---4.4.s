%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t4_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:52 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 342 expanded)
%              Number of leaves         :   87 ( 152 expanded)
%              Depth                    :    8
%              Number of atoms          :  513 ( 905 expanded)
%              Number of equality atoms :   21 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f247,f254,f261,f268,f275,f282,f289,f296,f303,f310,f317,f324,f331,f338,f345,f352,f359,f366,f373,f380,f387,f394,f401,f408,f415,f422,f429,f436,f443,f450,f457,f464,f471,f478,f485,f492,f499,f508,f517,f535,f551,f563,f573])).

fof(f573,plain,
    ( ~ spl18_0
    | ~ spl18_4
    | spl18_87 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_87 ),
    inference(subsumption_resolution,[],[f571,f562])).

fof(f562,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl18_87 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl18_87
  <=> ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_87])])).

fof(f571,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f569,f246])).

fof(f246,plain,
    ( l1_struct_0(sK0)
    | ~ spl18_0 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl18_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_0])])).

fof(f569,plain,
    ( ~ l1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl18_4 ),
    inference(resolution,[],[f187,f260])).

fof(f260,plain,
    ( v7_struct_0(sK0)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl18_4
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',fc7_struct_0)).

fof(f563,plain,
    ( ~ spl18_87
    | ~ spl18_2
    | spl18_7
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f555,f497,f266,f252,f561])).

fof(f252,plain,
    ( spl18_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f266,plain,
    ( spl18_7
  <=> ~ v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f497,plain,
    ( spl18_72
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_72])])).

fof(f555,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl18_2
    | ~ spl18_7
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f554,f267])).

fof(f267,plain,
    ( ~ v7_struct_0(sK1)
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f266])).

fof(f554,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl18_2
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f553,f253])).

fof(f253,plain,
    ( l1_struct_0(sK1)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f252])).

fof(f553,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl18_72 ),
    inference(superposition,[],[f184,f498])).

fof(f498,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl18_72 ),
    inference(avatar_component_clause,[],[f497])).

fof(f184,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',fc6_struct_0)).

fof(f551,plain,
    ( spl18_82
    | ~ spl18_85
    | ~ spl18_2
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f538,f497,f252,f549,f543])).

fof(f543,plain,
    ( spl18_82
  <=> v8_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_82])])).

fof(f549,plain,
    ( spl18_85
  <=> ~ v1_finset_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_85])])).

fof(f538,plain,
    ( ~ v1_finset_1(u1_struct_0(sK0))
    | v8_struct_0(sK1)
    | ~ spl18_2
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f537,f253])).

fof(f537,plain,
    ( ~ v1_finset_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v8_struct_0(sK1)
    | ~ spl18_72 ),
    inference(superposition,[],[f183,f498])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',fc9_struct_0)).

fof(f535,plain,
    ( spl18_78
    | ~ spl18_81
    | ~ spl18_2
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f522,f497,f252,f533,f527])).

fof(f527,plain,
    ( spl18_78
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_78])])).

fof(f533,plain,
    ( spl18_81
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_81])])).

fof(f522,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ spl18_2
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f521,f253])).

fof(f521,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_72 ),
    inference(superposition,[],[f182,f498])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',fc2_struct_0)).

fof(f517,plain,
    ( spl18_76
    | ~ spl18_12 ),
    inference(avatar_split_clause,[],[f509,f287,f515])).

fof(f515,plain,
    ( spl18_76
  <=> o_0_0_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_76])])).

fof(f287,plain,
    ( spl18_12
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f509,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl18_12 ),
    inference(resolution,[],[f238,f288])).

fof(f288,plain,
    ( v1_xboole_0(sK5)
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f287])).

fof(f238,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f181,f162])).

fof(f162,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',d2_xboole_0)).

fof(f181,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',t6_boole)).

fof(f508,plain,
    ( ~ spl18_75
    | spl18_63 ),
    inference(avatar_split_clause,[],[f501,f462,f506])).

fof(f506,plain,
    ( spl18_75
  <=> ~ v1_xboole_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_75])])).

fof(f462,plain,
    ( spl18_63
  <=> ~ v3_funct_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_63])])).

fof(f501,plain,
    ( ~ v1_xboole_0(sK16)
    | ~ spl18_63 ),
    inference(resolution,[],[f240,f463])).

fof(f463,plain,
    ( ~ v3_funct_1(sK16)
    | ~ spl18_63 ),
    inference(avatar_component_clause,[],[f462])).

fof(f240,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f239,f180])).

fof(f180,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',cc1_relat_1)).

fof(f239,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f195,f179])).

fof(f179,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',cc1_funct_1)).

fof(f195,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',cc4_funct_1)).

fof(f499,plain,(
    spl18_72 ),
    inference(avatar_split_clause,[],[f157,f497])).

fof(f157,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,
    ( ~ v7_struct_0(sK1)
    & v7_struct_0(sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f67,f121,f120])).

fof(f120,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v7_struct_0(X1)
            & v7_struct_0(X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(sK0)
          & u1_struct_0(sK0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
     => ( ~ v7_struct_0(sK1)
        & v7_struct_0(X0)
        & u1_struct_0(sK1) = u1_struct_0(X0)
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ( ( v7_struct_0(X0)
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => v7_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( ( v7_struct_0(X0)
              & u1_struct_0(X0) = u1_struct_0(X1) )
           => v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',t4_tex_2)).

fof(f492,plain,(
    spl18_70 ),
    inference(avatar_split_clause,[],[f162,f490])).

fof(f490,plain,
    ( spl18_70
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).

fof(f485,plain,(
    spl18_68 ),
    inference(avatar_split_clause,[],[f237,f483])).

fof(f483,plain,
    ( spl18_68
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_68])])).

fof(f237,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f160,f162])).

fof(f160,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',fc1_xboole_0)).

fof(f478,plain,(
    spl18_66 ),
    inference(avatar_split_clause,[],[f236,f476])).

fof(f476,plain,
    ( spl18_66
  <=> v1_funct_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_66])])).

fof(f236,plain,(
    v1_funct_1(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,
    ( v1_funct_1(sK17)
    & v1_relat_1(sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f64,f153])).

fof(f153,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK17)
      & v1_relat_1(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc2_funct_1)).

fof(f471,plain,(
    spl18_64 ),
    inference(avatar_split_clause,[],[f235,f469])).

fof(f469,plain,
    ( spl18_64
  <=> v1_relat_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_64])])).

fof(f235,plain,(
    v1_relat_1(sK17) ),
    inference(cnf_transformation,[],[f154])).

fof(f464,plain,(
    ~ spl18_63 ),
    inference(avatar_split_clause,[],[f234,f462])).

fof(f234,plain,(
    ~ v3_funct_1(sK16) ),
    inference(cnf_transformation,[],[f152])).

fof(f152,plain,
    ( ~ v3_funct_1(sK16)
    & v1_funct_1(sK16)
    & v1_relat_1(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f12,f151])).

fof(f151,plain,
    ( ? [X0] :
        ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v3_funct_1(sK16)
      & v1_funct_1(sK16)
      & v1_relat_1(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] :
      ( ~ v3_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc5_funct_1)).

fof(f457,plain,(
    spl18_60 ),
    inference(avatar_split_clause,[],[f233,f455])).

fof(f455,plain,
    ( spl18_60
  <=> v1_funct_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_60])])).

fof(f233,plain,(
    v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f152])).

fof(f450,plain,(
    spl18_58 ),
    inference(avatar_split_clause,[],[f232,f448])).

fof(f448,plain,
    ( spl18_58
  <=> v1_relat_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_58])])).

fof(f232,plain,(
    v1_relat_1(sK16) ),
    inference(cnf_transformation,[],[f152])).

fof(f443,plain,(
    spl18_56 ),
    inference(avatar_split_clause,[],[f231,f441])).

fof(f441,plain,
    ( spl18_56
  <=> v1_funct_1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_56])])).

fof(f231,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,plain,
    ( v1_funct_1(sK15)
    & v1_relat_1(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f22,f149])).

fof(f149,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK15)
      & v1_relat_1(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc1_funct_1)).

fof(f436,plain,(
    spl18_54 ),
    inference(avatar_split_clause,[],[f230,f434])).

fof(f434,plain,
    ( spl18_54
  <=> v1_relat_1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_54])])).

fof(f230,plain,(
    v1_relat_1(sK15) ),
    inference(cnf_transformation,[],[f150])).

fof(f429,plain,(
    spl18_52 ),
    inference(avatar_split_clause,[],[f229,f427])).

fof(f427,plain,
    ( spl18_52
  <=> v1_funct_1(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_52])])).

fof(f229,plain,(
    v1_funct_1(sK14) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,
    ( v1_funct_1(sK14)
    & v1_relat_1(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f60,f147])).

fof(f147,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK14)
      & v1_relat_1(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc3_funct_1)).

fof(f422,plain,(
    spl18_50 ),
    inference(avatar_split_clause,[],[f228,f420])).

fof(f420,plain,
    ( spl18_50
  <=> v1_relat_1(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_50])])).

fof(f228,plain,(
    v1_relat_1(sK14) ),
    inference(cnf_transformation,[],[f148])).

fof(f415,plain,(
    spl18_48 ),
    inference(avatar_split_clause,[],[f227,f413])).

fof(f413,plain,
    ( spl18_48
  <=> v1_relat_1(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_48])])).

fof(f227,plain,(
    v1_relat_1(sK13) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    v1_relat_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f63,f145])).

fof(f145,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK13) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ? [X0] :
      ( v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc2_relat_1)).

fof(f408,plain,(
    spl18_46 ),
    inference(avatar_split_clause,[],[f226,f406])).

fof(f406,plain,
    ( spl18_46
  <=> v7_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_46])])).

fof(f226,plain,(
    v7_struct_0(sK12) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,
    ( v7_struct_0(sK12)
    & ~ v2_struct_0(sK12)
    & l1_struct_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f51,f143])).

fof(f143,plain,
    ( ? [X0] :
        ( v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( v7_struct_0(sK12)
      & ~ v2_struct_0(sK12)
      & l1_struct_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f51,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc9_struct_0)).

fof(f401,plain,(
    ~ spl18_45 ),
    inference(avatar_split_clause,[],[f225,f399])).

fof(f399,plain,
    ( spl18_45
  <=> ~ v2_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_45])])).

fof(f225,plain,(
    ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f144])).

fof(f394,plain,(
    spl18_42 ),
    inference(avatar_split_clause,[],[f224,f392])).

fof(f392,plain,
    ( spl18_42
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_42])])).

fof(f224,plain,(
    l1_struct_0(sK12) ),
    inference(cnf_transformation,[],[f144])).

fof(f387,plain,(
    ~ spl18_41 ),
    inference(avatar_split_clause,[],[f223,f385])).

fof(f385,plain,
    ( spl18_41
  <=> ~ v7_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_41])])).

fof(f223,plain,(
    ~ v7_struct_0(sK11) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,
    ( ~ v7_struct_0(sK11)
    & ~ v2_struct_0(sK11)
    & l1_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f50,f141])).

fof(f141,plain,
    ( ? [X0] :
        ( ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( ~ v7_struct_0(sK11)
      & ~ v2_struct_0(sK11)
      & l1_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f50,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc10_struct_0)).

fof(f380,plain,(
    ~ spl18_39 ),
    inference(avatar_split_clause,[],[f222,f378])).

fof(f378,plain,
    ( spl18_39
  <=> ~ v2_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_39])])).

fof(f222,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f142])).

fof(f373,plain,(
    spl18_36 ),
    inference(avatar_split_clause,[],[f221,f371])).

fof(f371,plain,
    ( spl18_36
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_36])])).

fof(f221,plain,(
    l1_struct_0(sK11) ),
    inference(cnf_transformation,[],[f142])).

fof(f366,plain,(
    spl18_34 ),
    inference(avatar_split_clause,[],[f220,f364])).

fof(f364,plain,
    ( spl18_34
  <=> v1_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_34])])).

fof(f220,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,
    ( v1_funct_1(sK10)
    & v1_relat_1(sK10)
    & ~ v1_xboole_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f62,f139])).

fof(f139,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_funct_1(sK10)
      & v1_relat_1(sK10)
      & ~ v1_xboole_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc4_funct_1)).

fof(f359,plain,(
    spl18_32 ),
    inference(avatar_split_clause,[],[f219,f357])).

fof(f357,plain,
    ( spl18_32
  <=> v1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_32])])).

fof(f219,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f140])).

fof(f352,plain,(
    ~ spl18_31 ),
    inference(avatar_split_clause,[],[f218,f350])).

fof(f350,plain,
    ( spl18_31
  <=> ~ v1_xboole_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_31])])).

fof(f218,plain,(
    ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f140])).

fof(f345,plain,(
    spl18_28 ),
    inference(avatar_split_clause,[],[f217,f343])).

fof(f343,plain,
    ( spl18_28
  <=> v1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_28])])).

fof(f217,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,
    ( v1_relat_1(sK9)
    & ~ v1_xboole_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f23,f137])).

fof(f137,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK9)
      & ~ v1_xboole_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc1_relat_1)).

fof(f338,plain,(
    ~ spl18_27 ),
    inference(avatar_split_clause,[],[f216,f336])).

fof(f336,plain,
    ( spl18_27
  <=> ~ v1_xboole_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_27])])).

fof(f216,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f138])).

fof(f331,plain,(
    spl18_24 ),
    inference(avatar_split_clause,[],[f215,f329])).

fof(f329,plain,
    ( spl18_24
  <=> v1_zfmisc_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).

fof(f215,plain,(
    v1_zfmisc_1(sK8) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,
    ( v1_zfmisc_1(sK8)
    & ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f135])).

fof(f135,plain,
    ( ? [X0] :
        ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_zfmisc_1(sK8)
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f33,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc1_realset1)).

fof(f324,plain,(
    ~ spl18_23 ),
    inference(avatar_split_clause,[],[f214,f322])).

fof(f322,plain,
    ( spl18_23
  <=> ~ v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_23])])).

fof(f214,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f136])).

fof(f317,plain,(
    spl18_20 ),
    inference(avatar_split_clause,[],[f213,f315])).

fof(f315,plain,
    ( spl18_20
  <=> v4_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f213,plain,(
    v4_funct_1(sK7) ),
    inference(cnf_transformation,[],[f134])).

fof(f134,plain,
    ( v4_funct_1(sK7)
    & ~ v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f133])).

fof(f133,plain,
    ( ? [X0] :
        ( v4_funct_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v4_funct_1(sK7)
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc7_funct_1)).

fof(f310,plain,(
    ~ spl18_19 ),
    inference(avatar_split_clause,[],[f212,f308])).

fof(f308,plain,
    ( spl18_19
  <=> ~ v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_19])])).

fof(f212,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f134])).

fof(f303,plain,(
    ~ spl18_17 ),
    inference(avatar_split_clause,[],[f211,f301])).

fof(f301,plain,
    ( spl18_17
  <=> ~ v1_zfmisc_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_17])])).

fof(f211,plain,(
    ~ v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,plain,
    ( ~ v1_zfmisc_1(sK6)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f131])).

fof(f131,plain,
    ( ? [X0] :
        ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ~ v1_zfmisc_1(sK6)
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc2_realset1)).

fof(f296,plain,(
    ~ spl18_15 ),
    inference(avatar_split_clause,[],[f210,f294])).

fof(f294,plain,
    ( spl18_15
  <=> ~ v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_15])])).

fof(f210,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f132])).

fof(f289,plain,(
    spl18_12 ),
    inference(avatar_split_clause,[],[f209,f287])).

fof(f209,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f129])).

fof(f129,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f34,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc1_xboole_0)).

fof(f282,plain,(
    spl18_10 ),
    inference(avatar_split_clause,[],[f208,f280])).

fof(f280,plain,
    ( spl18_10
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f208,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f127])).

fof(f127,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f52,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',existence_l1_struct_0)).

fof(f275,plain,(
    ~ spl18_9 ),
    inference(avatar_split_clause,[],[f207,f273])).

fof(f273,plain,
    ( spl18_9
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f207,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f125])).

fof(f125,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f36,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t4_tex_2.p',rc2_xboole_0)).

fof(f268,plain,(
    ~ spl18_7 ),
    inference(avatar_split_clause,[],[f159,f266])).

fof(f159,plain,(
    ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f122])).

fof(f261,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f158,f259])).

fof(f158,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f122])).

fof(f254,plain,(
    spl18_2 ),
    inference(avatar_split_clause,[],[f156,f252])).

fof(f156,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f122])).

fof(f247,plain,(
    spl18_0 ),
    inference(avatar_split_clause,[],[f155,f245])).

fof(f155,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f122])).
%------------------------------------------------------------------------------
