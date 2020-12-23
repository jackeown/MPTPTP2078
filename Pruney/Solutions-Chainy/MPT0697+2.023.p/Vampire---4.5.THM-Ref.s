%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 332 expanded)
%              Number of leaves         :   49 ( 159 expanded)
%              Depth                    :    7
%              Number of atoms          :  502 ( 882 expanded)
%              Number of equality atoms :   84 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3738,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f78,f82,f87,f92,f96,f100,f104,f108,f112,f128,f137,f146,f156,f213,f258,f533,f537,f546,f586,f590,f619,f697,f703,f858,f1004,f1431,f2190,f2204,f2250,f3094,f3497,f3534,f3564,f3708])).

fof(f3708,plain,
    ( ~ spl2_5
    | spl2_28
    | ~ spl2_128 ),
    inference(avatar_contradiction_clause,[],[f3697])).

fof(f3697,plain,
    ( $false
    | ~ spl2_5
    | spl2_28
    | ~ spl2_128 ),
    inference(subsumption_resolution,[],[f257,f3644])).

fof(f3644,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)
    | ~ spl2_5
    | ~ spl2_128 ),
    inference(superposition,[],[f3563,f77])).

fof(f77,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_5
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3563,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f3562])).

fof(f3562,plain,
    ( spl2_128
  <=> ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f257,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl2_28
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f3564,plain,
    ( spl2_128
    | ~ spl2_12
    | ~ spl2_126 ),
    inference(avatar_split_clause,[],[f3539,f3532,f106,f3562])).

fof(f106,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f3532,plain,
    ( spl2_126
  <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).

fof(f3539,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)
    | ~ spl2_12
    | ~ spl2_126 ),
    inference(resolution,[],[f3533,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f3533,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl2_126 ),
    inference(avatar_component_clause,[],[f3532])).

fof(f3534,plain,
    ( spl2_126
    | ~ spl2_48
    | ~ spl2_80
    | ~ spl2_110
    | ~ spl2_125 ),
    inference(avatar_split_clause,[],[f3530,f3495,f2247,f1002,f617,f3532])).

fof(f617,plain,
    ( spl2_48
  <=> ! [X5,X6] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1002,plain,
    ( spl2_80
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f2247,plain,
    ( spl2_110
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).

fof(f3495,plain,
    ( spl2_125
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f3530,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl2_48
    | ~ spl2_80
    | ~ spl2_110
    | ~ spl2_125 ),
    inference(forward_demodulation,[],[f3529,f2249])).

fof(f2249,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_110 ),
    inference(avatar_component_clause,[],[f2247])).

fof(f3529,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_48
    | ~ spl2_80
    | ~ spl2_125 ),
    inference(subsumption_resolution,[],[f3515,f618])).

fof(f618,plain,
    ( ! [X6,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f617])).

fof(f3515,plain,
    ( ! [X11] :
        ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
        | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) )
    | ~ spl2_80
    | ~ spl2_125 ),
    inference(superposition,[],[f1003,f3496])).

fof(f3496,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f1003,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f3497,plain,
    ( spl2_125
    | ~ spl2_57
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f3097,f3092,f701,f3495])).

fof(f701,plain,
    ( spl2_57
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f3092,plain,
    ( spl2_120
  <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f3097,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl2_57
    | ~ spl2_120 ),
    inference(superposition,[],[f3093,f702])).

fof(f702,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f701])).

fof(f3093,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f3092])).

fof(f3094,plain,
    ( spl2_120
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_107 ),
    inference(avatar_split_clause,[],[f2902,f2188,f67,f62,f57,f3092])).

fof(f57,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2188,plain,
    ( spl2_107
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f2902,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_107 ),
    inference(subsumption_resolution,[],[f2901,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f2901,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_107 ),
    inference(subsumption_resolution,[],[f2900,f64])).

fof(f64,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f2900,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_107 ),
    inference(resolution,[],[f2189,f69])).

fof(f69,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f2189,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f2250,plain,
    ( spl2_110
    | ~ spl2_25
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f2243,f2202,f211,f2247])).

fof(f211,plain,
    ( spl2_25
  <=> ! [X6] : k1_xboole_0 = k6_subset_1(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2202,plain,
    ( spl2_109
  <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f2243,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_25
    | ~ spl2_109 ),
    inference(forward_demodulation,[],[f2206,f212])).

fof(f212,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(X6,X6)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f2206,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X3,X3))
    | ~ spl2_25
    | ~ spl2_109 ),
    inference(superposition,[],[f2203,f212])).

fof(f2203,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2204,plain,
    ( spl2_109
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_86 ),
    inference(avatar_split_clause,[],[f1767,f1429,f62,f57,f2202])).

fof(f1429,plain,
    ( spl2_86
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f1767,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_86 ),
    inference(subsumption_resolution,[],[f1766,f59])).

fof(f1766,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_86 ),
    inference(resolution,[],[f1430,f64])).

fof(f1430,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1429])).

fof(f2190,plain,(
    spl2_107 ),
    inference(avatar_split_clause,[],[f50,f2188])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f1431,plain,(
    spl2_86 ),
    inference(avatar_split_clause,[],[f49,f1429])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1004,plain,
    ( spl2_80
    | ~ spl2_1
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f1000,f856,f57,f1002])).

fof(f856,plain,
    ( spl2_66
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f1000,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_1
    | ~ spl2_66 ),
    inference(resolution,[],[f857,f59])).

fof(f857,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f856])).

fof(f858,plain,(
    spl2_66 ),
    inference(avatar_split_clause,[],[f42,f856])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f703,plain,
    ( spl2_57
    | ~ spl2_12
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f698,f695,f106,f701])).

fof(f695,plain,
    ( spl2_56
  <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f698,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_12
    | ~ spl2_56 ),
    inference(resolution,[],[f696,f107])).

fof(f696,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f695])).

fof(f697,plain,
    ( spl2_56
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f693,f588,f62,f57,f695])).

fof(f588,plain,
    ( spl2_45
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f693,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f692,f59])).

fof(f692,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(resolution,[],[f589,f64])).

fof(f589,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f588])).

fof(f619,plain,
    ( spl2_48
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f594,f584,f154,f617])).

fof(f154,plain,
    ( spl2_19
  <=> ! [X5,X4,X6] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f584,plain,
    ( spl2_44
  <=> ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f594,plain,
    ( ! [X6,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(superposition,[],[f155,f585])).

fof(f585,plain,
    ( ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f584])).

fof(f155,plain,
    ( ! [X6,X4,X5] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f590,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f44,f588])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f586,plain,
    ( spl2_44
    | ~ spl2_41
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f575,f544,f535,f584])).

fof(f535,plain,
    ( spl2_41
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f544,plain,
    ( spl2_43
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f575,plain,
    ( ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))
    | ~ spl2_41
    | ~ spl2_43 ),
    inference(trivial_inequality_removal,[],[f574])).

fof(f574,plain,
    ( ! [X16] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1)) )
    | ~ spl2_41
    | ~ spl2_43 ),
    inference(superposition,[],[f536,f545])).

fof(f545,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f544])).

fof(f536,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f535])).

fof(f546,plain,
    ( spl2_43
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f542,f531,f57,f544])).

fof(f531,plain,
    ( spl2_40
  <=> ! [X18,X17] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17))
        | ~ v1_relat_1(X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f542,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(resolution,[],[f532,f59])).

fof(f532,plain,
    ( ! [X17,X18] :
        ( ~ v1_relat_1(X17)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17)) )
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f531])).

fof(f537,plain,
    ( spl2_41
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f252,f110,f98,f535])).

fof(f98,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f110,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f252,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 )
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(resolution,[],[f111,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f533,plain,
    ( spl2_40
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f196,f106,f94,f531])).

fof(f94,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f196,plain,
    ( ! [X17,X18] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17))
        | ~ v1_relat_1(X17) )
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(resolution,[],[f107,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f258,plain,
    ( ~ spl2_28
    | spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f250,f110,f89,f255])).

fof(f89,plain,
    ( spl2_8
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f250,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_8
    | ~ spl2_13 ),
    inference(resolution,[],[f111,f91])).

fof(f91,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f213,plain,
    ( spl2_25
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f191,f106,f85,f211])).

fof(f85,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f191,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(X6,X6)
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(resolution,[],[f107,f86])).

fof(f86,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f156,plain,
    ( spl2_19
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f151,f144,f126,f154])).

fof(f126,plain,
    ( spl2_16
  <=> ! [X1,X2] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f144,plain,
    ( spl2_18
  <=> ! [X3,X2,X4] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f151,plain,
    ( ! [X6,X4,X5] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(superposition,[],[f145,f127])).

fof(f127,plain,
    ( ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f145,plain,
    ( ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl2_18
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f139,f135,f102,f144])).

fof(f102,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f135,plain,
    ( spl2_17
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f139,plain,
    ( ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(resolution,[],[f136,f103])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f136,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl2_17
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f130,f102,f85,f135])).

fof(f130,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(resolution,[],[f103,f86])).

fof(f128,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f114,f98,f80,f126])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f114,plain,
    ( ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(resolution,[],[f99,f81])).

fof(f81,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f112,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f108,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f53,f106])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f100,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f43,f98])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f96,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f92,plain,(
    ~ spl2_8 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f87,plain,
    ( spl2_7
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f80,f76,f85])).

fof(f83,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f81,f77])).

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f52,f80])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f78,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f51,f76])).

fof(f51,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f70,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17167)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (17165)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17171)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17168)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (17181)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (17182)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (17170)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17176)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (17179)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (17173)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (17175)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (17169)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (17174)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (17180)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (17166)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (17172)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (17178)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (17177)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.19/0.65  % (17172)Refutation found. Thanks to Tanya!
% 2.19/0.65  % SZS status Theorem for theBenchmark
% 2.19/0.65  % SZS output start Proof for theBenchmark
% 2.19/0.65  fof(f3738,plain,(
% 2.19/0.65    $false),
% 2.19/0.65    inference(avatar_sat_refutation,[],[f60,f65,f70,f78,f82,f87,f92,f96,f100,f104,f108,f112,f128,f137,f146,f156,f213,f258,f533,f537,f546,f586,f590,f619,f697,f703,f858,f1004,f1431,f2190,f2204,f2250,f3094,f3497,f3534,f3564,f3708])).
% 2.19/0.65  fof(f3708,plain,(
% 2.19/0.65    ~spl2_5 | spl2_28 | ~spl2_128),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f3697])).
% 2.19/0.65  fof(f3697,plain,(
% 2.19/0.65    $false | (~spl2_5 | spl2_28 | ~spl2_128)),
% 2.19/0.65    inference(subsumption_resolution,[],[f257,f3644])).
% 2.19/0.65  fof(f3644,plain,(
% 2.19/0.65    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ) | (~spl2_5 | ~spl2_128)),
% 2.19/0.65    inference(superposition,[],[f3563,f77])).
% 2.19/0.65  fof(f77,plain,(
% 2.19/0.65    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 2.19/0.65    inference(avatar_component_clause,[],[f76])).
% 2.19/0.65  fof(f76,plain,(
% 2.19/0.65    spl2_5 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.19/0.65  fof(f3563,plain,(
% 2.19/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)) ) | ~spl2_128),
% 2.19/0.65    inference(avatar_component_clause,[],[f3562])).
% 2.19/0.65  fof(f3562,plain,(
% 2.19/0.65    spl2_128 <=> ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 2.19/0.65  fof(f257,plain,(
% 2.19/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_28),
% 2.19/0.65    inference(avatar_component_clause,[],[f255])).
% 2.19/0.65  fof(f255,plain,(
% 2.19/0.65    spl2_28 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.19/0.65  fof(f3564,plain,(
% 2.19/0.65    spl2_128 | ~spl2_12 | ~spl2_126),
% 2.19/0.65    inference(avatar_split_clause,[],[f3539,f3532,f106,f3562])).
% 2.19/0.65  fof(f106,plain,(
% 2.19/0.65    spl2_12 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.19/0.65  fof(f3532,plain,(
% 2.19/0.65    spl2_126 <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).
% 2.19/0.65  fof(f3539,plain,(
% 2.19/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)) ) | (~spl2_12 | ~spl2_126)),
% 2.19/0.65    inference(resolution,[],[f3533,f107])).
% 2.19/0.65  fof(f107,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl2_12),
% 2.19/0.65    inference(avatar_component_clause,[],[f106])).
% 2.19/0.65  fof(f3533,plain,(
% 2.19/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | ~spl2_126),
% 2.19/0.65    inference(avatar_component_clause,[],[f3532])).
% 2.19/0.65  fof(f3534,plain,(
% 2.19/0.65    spl2_126 | ~spl2_48 | ~spl2_80 | ~spl2_110 | ~spl2_125),
% 2.19/0.65    inference(avatar_split_clause,[],[f3530,f3495,f2247,f1002,f617,f3532])).
% 2.19/0.65  fof(f617,plain,(
% 2.19/0.65    spl2_48 <=> ! [X5,X6] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 2.19/0.65  fof(f1002,plain,(
% 2.19/0.65    spl2_80 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 2.19/0.65  fof(f2247,plain,(
% 2.19/0.65    spl2_110 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).
% 2.19/0.65  fof(f3495,plain,(
% 2.19/0.65    spl2_125 <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).
% 2.19/0.65  fof(f3530,plain,(
% 2.19/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | (~spl2_48 | ~spl2_80 | ~spl2_110 | ~spl2_125)),
% 2.19/0.65    inference(forward_demodulation,[],[f3529,f2249])).
% 2.19/0.65  fof(f2249,plain,(
% 2.19/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_110),
% 2.19/0.65    inference(avatar_component_clause,[],[f2247])).
% 2.19/0.65  fof(f3529,plain,(
% 2.19/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl2_48 | ~spl2_80 | ~spl2_125)),
% 2.19/0.65    inference(subsumption_resolution,[],[f3515,f618])).
% 2.19/0.65  fof(f618,plain,(
% 2.19/0.65    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))) ) | ~spl2_48),
% 2.19/0.65    inference(avatar_component_clause,[],[f617])).
% 2.19/0.65  fof(f3515,plain,(
% 2.19/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) ) | (~spl2_80 | ~spl2_125)),
% 2.19/0.65    inference(superposition,[],[f1003,f3496])).
% 2.19/0.65  fof(f3496,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | ~spl2_125),
% 2.19/0.65    inference(avatar_component_clause,[],[f3495])).
% 2.19/0.65  fof(f1003,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl2_80),
% 2.19/0.65    inference(avatar_component_clause,[],[f1002])).
% 2.19/0.65  fof(f3497,plain,(
% 2.19/0.65    spl2_125 | ~spl2_57 | ~spl2_120),
% 2.19/0.65    inference(avatar_split_clause,[],[f3097,f3092,f701,f3495])).
% 2.19/0.65  fof(f701,plain,(
% 2.19/0.65    spl2_57 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 2.19/0.65  fof(f3092,plain,(
% 2.19/0.65    spl2_120 <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 2.19/0.65  fof(f3097,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | (~spl2_57 | ~spl2_120)),
% 2.19/0.65    inference(superposition,[],[f3093,f702])).
% 2.19/0.65  fof(f702,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_57),
% 2.19/0.65    inference(avatar_component_clause,[],[f701])).
% 2.19/0.65  fof(f3093,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl2_120),
% 2.19/0.65    inference(avatar_component_clause,[],[f3092])).
% 2.19/0.65  fof(f3094,plain,(
% 2.19/0.65    spl2_120 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_107),
% 2.19/0.65    inference(avatar_split_clause,[],[f2902,f2188,f67,f62,f57,f3092])).
% 2.19/0.65  fof(f57,plain,(
% 2.19/0.65    spl2_1 <=> v1_relat_1(sK1)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.19/0.65  fof(f62,plain,(
% 2.19/0.65    spl2_2 <=> v1_funct_1(sK1)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.19/0.65  fof(f67,plain,(
% 2.19/0.65    spl2_3 <=> v2_funct_1(sK1)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.19/0.65  fof(f2188,plain,(
% 2.19/0.65    spl2_107 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 2.19/0.65  fof(f2902,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_107)),
% 2.19/0.65    inference(subsumption_resolution,[],[f2901,f59])).
% 2.19/0.65  fof(f59,plain,(
% 2.19/0.65    v1_relat_1(sK1) | ~spl2_1),
% 2.19/0.65    inference(avatar_component_clause,[],[f57])).
% 2.19/0.65  fof(f2901,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_107)),
% 2.19/0.65    inference(subsumption_resolution,[],[f2900,f64])).
% 2.19/0.65  fof(f64,plain,(
% 2.19/0.65    v1_funct_1(sK1) | ~spl2_2),
% 2.19/0.65    inference(avatar_component_clause,[],[f62])).
% 2.19/0.65  fof(f2900,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_107)),
% 2.19/0.65    inference(resolution,[],[f2189,f69])).
% 2.19/0.65  fof(f69,plain,(
% 2.19/0.65    v2_funct_1(sK1) | ~spl2_3),
% 2.19/0.65    inference(avatar_component_clause,[],[f67])).
% 2.19/0.65  fof(f2189,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl2_107),
% 2.19/0.65    inference(avatar_component_clause,[],[f2188])).
% 2.19/0.65  fof(f2250,plain,(
% 2.19/0.65    spl2_110 | ~spl2_25 | ~spl2_109),
% 2.19/0.65    inference(avatar_split_clause,[],[f2243,f2202,f211,f2247])).
% 2.19/0.65  fof(f211,plain,(
% 2.19/0.65    spl2_25 <=> ! [X6] : k1_xboole_0 = k6_subset_1(X6,X6)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 2.19/0.65  fof(f2202,plain,(
% 2.19/0.65    spl2_109 <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 2.19/0.65  fof(f2243,plain,(
% 2.19/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl2_25 | ~spl2_109)),
% 2.19/0.65    inference(forward_demodulation,[],[f2206,f212])).
% 2.19/0.65  fof(f212,plain,(
% 2.19/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(X6,X6)) ) | ~spl2_25),
% 2.19/0.65    inference(avatar_component_clause,[],[f211])).
% 2.19/0.65  fof(f2206,plain,(
% 2.19/0.65    ( ! [X3] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X3,X3))) ) | (~spl2_25 | ~spl2_109)),
% 2.19/0.65    inference(superposition,[],[f2203,f212])).
% 2.19/0.65  fof(f2203,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | ~spl2_109),
% 2.19/0.65    inference(avatar_component_clause,[],[f2202])).
% 2.19/0.65  fof(f2204,plain,(
% 2.19/0.65    spl2_109 | ~spl2_1 | ~spl2_2 | ~spl2_86),
% 2.19/0.65    inference(avatar_split_clause,[],[f1767,f1429,f62,f57,f2202])).
% 2.19/0.65  fof(f1429,plain,(
% 2.19/0.65    spl2_86 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 2.19/0.65  fof(f1767,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_86)),
% 2.19/0.65    inference(subsumption_resolution,[],[f1766,f59])).
% 2.19/0.65  fof(f1766,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_86)),
% 2.19/0.65    inference(resolution,[],[f1430,f64])).
% 2.19/0.65  fof(f1430,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl2_86),
% 2.19/0.65    inference(avatar_component_clause,[],[f1429])).
% 2.19/0.65  fof(f2190,plain,(
% 2.19/0.65    spl2_107),
% 2.19/0.65    inference(avatar_split_clause,[],[f50,f2188])).
% 2.19/0.65  fof(f50,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f29])).
% 2.19/0.65  fof(f29,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/0.65    inference(flattening,[],[f28])).
% 2.19/0.65  fof(f28,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.19/0.65    inference(ennf_transformation,[],[f10])).
% 2.19/0.65  fof(f10,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 2.19/0.65  fof(f1431,plain,(
% 2.19/0.65    spl2_86),
% 2.19/0.65    inference(avatar_split_clause,[],[f49,f1429])).
% 2.19/0.65  fof(f49,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f27])).
% 2.19/0.65  fof(f27,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/0.65    inference(flattening,[],[f26])).
% 2.19/0.65  fof(f26,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.19/0.65    inference(ennf_transformation,[],[f11])).
% 2.19/0.65  fof(f11,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 2.19/0.65  fof(f1004,plain,(
% 2.19/0.65    spl2_80 | ~spl2_1 | ~spl2_66),
% 2.19/0.65    inference(avatar_split_clause,[],[f1000,f856,f57,f1002])).
% 2.19/0.65  fof(f856,plain,(
% 2.19/0.65    spl2_66 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 2.19/0.65  fof(f1000,plain,(
% 2.19/0.65    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_66)),
% 2.19/0.65    inference(resolution,[],[f857,f59])).
% 2.19/0.65  fof(f857,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl2_66),
% 2.19/0.65    inference(avatar_component_clause,[],[f856])).
% 2.19/0.65  fof(f858,plain,(
% 2.19/0.65    spl2_66),
% 2.19/0.65    inference(avatar_split_clause,[],[f42,f856])).
% 2.19/0.65  fof(f42,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f20])).
% 2.19/0.65  fof(f20,plain,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.19/0.65    inference(flattening,[],[f19])).
% 2.19/0.65  fof(f19,plain,(
% 2.19/0.65    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.19/0.65    inference(ennf_transformation,[],[f13])).
% 2.19/0.65  fof(f13,axiom,(
% 2.19/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.19/0.65  fof(f703,plain,(
% 2.19/0.65    spl2_57 | ~spl2_12 | ~spl2_56),
% 2.19/0.65    inference(avatar_split_clause,[],[f698,f695,f106,f701])).
% 2.19/0.65  fof(f695,plain,(
% 2.19/0.65    spl2_56 <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 2.19/0.65  fof(f698,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_12 | ~spl2_56)),
% 2.19/0.65    inference(resolution,[],[f696,f107])).
% 2.19/0.65  fof(f696,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_56),
% 2.19/0.65    inference(avatar_component_clause,[],[f695])).
% 2.19/0.65  fof(f697,plain,(
% 2.19/0.65    spl2_56 | ~spl2_1 | ~spl2_2 | ~spl2_45),
% 2.19/0.65    inference(avatar_split_clause,[],[f693,f588,f62,f57,f695])).
% 2.19/0.65  fof(f588,plain,(
% 2.19/0.65    spl2_45 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 2.19/0.65  fof(f693,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_45)),
% 2.19/0.65    inference(subsumption_resolution,[],[f692,f59])).
% 2.19/0.65  fof(f692,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_45)),
% 2.19/0.65    inference(resolution,[],[f589,f64])).
% 2.19/0.65  fof(f589,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_45),
% 2.19/0.65    inference(avatar_component_clause,[],[f588])).
% 2.19/0.65  fof(f619,plain,(
% 2.19/0.65    spl2_48 | ~spl2_19 | ~spl2_44),
% 2.19/0.65    inference(avatar_split_clause,[],[f594,f584,f154,f617])).
% 2.19/0.65  fof(f154,plain,(
% 2.19/0.65    spl2_19 <=> ! [X5,X4,X6] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.19/0.65  fof(f584,plain,(
% 2.19/0.65    spl2_44 <=> ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 2.19/0.65  fof(f594,plain,(
% 2.19/0.65    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))) ) | (~spl2_19 | ~spl2_44)),
% 2.19/0.65    inference(superposition,[],[f155,f585])).
% 2.19/0.65  fof(f585,plain,(
% 2.19/0.65    ( ! [X16] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | ~spl2_44),
% 2.19/0.65    inference(avatar_component_clause,[],[f584])).
% 2.19/0.65  fof(f155,plain,(
% 2.19/0.65    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))) ) | ~spl2_19),
% 2.19/0.65    inference(avatar_component_clause,[],[f154])).
% 2.19/0.65  fof(f590,plain,(
% 2.19/0.65    spl2_45),
% 2.19/0.65    inference(avatar_split_clause,[],[f44,f588])).
% 2.19/0.65  fof(f44,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f23])).
% 2.19/0.65  fof(f23,plain,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.19/0.65    inference(flattening,[],[f22])).
% 2.19/0.65  fof(f22,plain,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f12])).
% 2.19/0.65  fof(f12,axiom,(
% 2.19/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.19/0.65  fof(f586,plain,(
% 2.19/0.65    spl2_44 | ~spl2_41 | ~spl2_43),
% 2.19/0.65    inference(avatar_split_clause,[],[f575,f544,f535,f584])).
% 2.19/0.65  fof(f535,plain,(
% 2.19/0.65    spl2_41 <=> ! [X3,X2] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 2.19/0.65  fof(f544,plain,(
% 2.19/0.65    spl2_43 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 2.19/0.65  fof(f575,plain,(
% 2.19/0.65    ( ! [X16] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | (~spl2_41 | ~spl2_43)),
% 2.19/0.65    inference(trivial_inequality_removal,[],[f574])).
% 2.19/0.65  fof(f574,plain,(
% 2.19/0.65    ( ! [X16] : (k1_xboole_0 != k1_xboole_0 | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | (~spl2_41 | ~spl2_43)),
% 2.19/0.65    inference(superposition,[],[f536,f545])).
% 2.19/0.65  fof(f545,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_43),
% 2.19/0.65    inference(avatar_component_clause,[],[f544])).
% 2.19/0.65  fof(f536,plain,(
% 2.19/0.65    ( ! [X2,X3] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3) ) | ~spl2_41),
% 2.19/0.65    inference(avatar_component_clause,[],[f535])).
% 2.19/0.65  fof(f546,plain,(
% 2.19/0.65    spl2_43 | ~spl2_1 | ~spl2_40),
% 2.19/0.65    inference(avatar_split_clause,[],[f542,f531,f57,f544])).
% 2.19/0.65  fof(f531,plain,(
% 2.19/0.65    spl2_40 <=> ! [X18,X17] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17)) | ~v1_relat_1(X17))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 2.19/0.65  fof(f542,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_40)),
% 2.19/0.65    inference(resolution,[],[f532,f59])).
% 2.19/0.65  fof(f532,plain,(
% 2.19/0.65    ( ! [X17,X18] : (~v1_relat_1(X17) | k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17))) ) | ~spl2_40),
% 2.19/0.65    inference(avatar_component_clause,[],[f531])).
% 2.19/0.65  fof(f537,plain,(
% 2.19/0.65    spl2_41 | ~spl2_10 | ~spl2_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f252,f110,f98,f535])).
% 2.19/0.65  fof(f98,plain,(
% 2.19/0.65    spl2_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.19/0.65  fof(f110,plain,(
% 2.19/0.65    spl2_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.19/0.65  fof(f252,plain,(
% 2.19/0.65    ( ! [X2,X3] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3) ) | (~spl2_10 | ~spl2_13)),
% 2.19/0.65    inference(resolution,[],[f111,f99])).
% 2.19/0.65  fof(f99,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_10),
% 2.19/0.65    inference(avatar_component_clause,[],[f98])).
% 2.19/0.65  fof(f111,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) ) | ~spl2_13),
% 2.19/0.65    inference(avatar_component_clause,[],[f110])).
% 2.19/0.65  fof(f533,plain,(
% 2.19/0.65    spl2_40 | ~spl2_9 | ~spl2_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f196,f106,f94,f531])).
% 2.19/0.65  fof(f94,plain,(
% 2.19/0.65    spl2_9 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.19/0.65  fof(f196,plain,(
% 2.19/0.65    ( ! [X17,X18] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X17,X18),k1_relat_1(X17)) | ~v1_relat_1(X17)) ) | (~spl2_9 | ~spl2_12)),
% 2.19/0.65    inference(resolution,[],[f107,f95])).
% 2.19/0.65  fof(f95,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_9),
% 2.19/0.65    inference(avatar_component_clause,[],[f94])).
% 2.19/0.65  fof(f258,plain,(
% 2.19/0.65    ~spl2_28 | spl2_8 | ~spl2_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f250,f110,f89,f255])).
% 2.19/0.65  fof(f89,plain,(
% 2.19/0.65    spl2_8 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.19/0.65  fof(f250,plain,(
% 2.19/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | (spl2_8 | ~spl2_13)),
% 2.19/0.65    inference(resolution,[],[f111,f91])).
% 2.19/0.65  fof(f91,plain,(
% 2.19/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_8),
% 2.19/0.65    inference(avatar_component_clause,[],[f89])).
% 2.19/0.65  fof(f213,plain,(
% 2.19/0.65    spl2_25 | ~spl2_7 | ~spl2_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f191,f106,f85,f211])).
% 2.19/0.65  fof(f85,plain,(
% 2.19/0.65    spl2_7 <=> ! [X0] : r1_tarski(X0,X0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.19/0.65  fof(f191,plain,(
% 2.19/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(X6,X6)) ) | (~spl2_7 | ~spl2_12)),
% 2.19/0.65    inference(resolution,[],[f107,f86])).
% 2.19/0.65  fof(f86,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_7),
% 2.19/0.65    inference(avatar_component_clause,[],[f85])).
% 2.19/0.65  fof(f156,plain,(
% 2.19/0.65    spl2_19 | ~spl2_16 | ~spl2_18),
% 2.19/0.65    inference(avatar_split_clause,[],[f151,f144,f126,f154])).
% 2.19/0.65  fof(f126,plain,(
% 2.19/0.65    spl2_16 <=> ! [X1,X2] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.19/0.65  fof(f144,plain,(
% 2.19/0.65    spl2_18 <=> ! [X3,X2,X4] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.19/0.65  fof(f151,plain,(
% 2.19/0.65    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))) ) | (~spl2_16 | ~spl2_18)),
% 2.19/0.65    inference(superposition,[],[f145,f127])).
% 2.19/0.65  fof(f127,plain,(
% 2.19/0.65    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),X1) = X1) ) | ~spl2_16),
% 2.19/0.65    inference(avatar_component_clause,[],[f126])).
% 2.19/0.65  fof(f145,plain,(
% 2.19/0.65    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ) | ~spl2_18),
% 2.19/0.65    inference(avatar_component_clause,[],[f144])).
% 2.19/0.65  fof(f146,plain,(
% 2.19/0.65    spl2_18 | ~spl2_11 | ~spl2_17),
% 2.19/0.65    inference(avatar_split_clause,[],[f139,f135,f102,f144])).
% 2.19/0.65  fof(f102,plain,(
% 2.19/0.65    spl2_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.19/0.65  fof(f135,plain,(
% 2.19/0.65    spl2_17 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.19/0.65  fof(f139,plain,(
% 2.19/0.65    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ) | (~spl2_11 | ~spl2_17)),
% 2.19/0.65    inference(resolution,[],[f136,f103])).
% 2.19/0.65  fof(f103,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_11),
% 2.19/0.65    inference(avatar_component_clause,[],[f102])).
% 2.19/0.65  fof(f136,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_17),
% 2.19/0.65    inference(avatar_component_clause,[],[f135])).
% 2.19/0.65  fof(f137,plain,(
% 2.19/0.65    spl2_17 | ~spl2_7 | ~spl2_11),
% 2.19/0.65    inference(avatar_split_clause,[],[f130,f102,f85,f135])).
% 2.19/0.65  fof(f130,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_11)),
% 2.19/0.65    inference(resolution,[],[f103,f86])).
% 2.19/0.65  fof(f128,plain,(
% 2.19/0.65    spl2_16 | ~spl2_6 | ~spl2_10),
% 2.19/0.65    inference(avatar_split_clause,[],[f114,f98,f80,f126])).
% 2.19/0.65  fof(f80,plain,(
% 2.19/0.65    spl2_6 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.19/0.65  fof(f114,plain,(
% 2.19/0.65    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),X1) = X1) ) | (~spl2_6 | ~spl2_10)),
% 2.19/0.65    inference(resolution,[],[f99,f81])).
% 2.19/0.65  fof(f81,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl2_6),
% 2.19/0.65    inference(avatar_component_clause,[],[f80])).
% 2.19/0.65  fof(f112,plain,(
% 2.19/0.65    spl2_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f54,f110])).
% 2.19/0.65  fof(f54,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 2.19/0.65    inference(definition_unfolding,[],[f45,f40])).
% 2.19/0.65  fof(f40,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f8])).
% 2.19/0.65  fof(f8,axiom,(
% 2.19/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.19/0.65  fof(f45,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.19/0.65    inference(cnf_transformation,[],[f32])).
% 2.19/0.65  fof(f32,plain,(
% 2.19/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.19/0.65    inference(nnf_transformation,[],[f1])).
% 2.19/0.65  fof(f1,axiom,(
% 2.19/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.19/0.65  fof(f108,plain,(
% 2.19/0.65    spl2_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f53,f106])).
% 2.19/0.65  fof(f53,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.19/0.65    inference(definition_unfolding,[],[f46,f40])).
% 2.19/0.65  fof(f46,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f32])).
% 2.19/0.65  fof(f104,plain,(
% 2.19/0.65    spl2_11),
% 2.19/0.65    inference(avatar_split_clause,[],[f48,f102])).
% 2.19/0.65  fof(f48,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f25])).
% 2.19/0.65  fof(f25,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.19/0.65    inference(ennf_transformation,[],[f2])).
% 2.19/0.65  fof(f2,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.19/0.65  fof(f100,plain,(
% 2.19/0.65    spl2_10),
% 2.19/0.65    inference(avatar_split_clause,[],[f43,f98])).
% 2.19/0.65  fof(f43,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f21])).
% 2.19/0.65  fof(f21,plain,(
% 2.19/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.19/0.65    inference(ennf_transformation,[],[f3])).
% 2.19/0.65  fof(f3,axiom,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.19/0.65  fof(f96,plain,(
% 2.19/0.65    spl2_9),
% 2.19/0.65    inference(avatar_split_clause,[],[f41,f94])).
% 2.19/0.65  fof(f41,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f18])).
% 2.19/0.65  fof(f18,plain,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.19/0.65    inference(ennf_transformation,[],[f9])).
% 2.19/0.65  fof(f9,axiom,(
% 2.19/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.19/0.65  fof(f92,plain,(
% 2.19/0.65    ~spl2_8),
% 2.19/0.65    inference(avatar_split_clause,[],[f36,f89])).
% 2.19/0.65  fof(f36,plain,(
% 2.19/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f31])).
% 2.19/0.65  fof(f31,plain,(
% 2.19/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).
% 2.19/0.65  fof(f30,plain,(
% 2.19/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f17,plain,(
% 2.19/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.19/0.65    inference(flattening,[],[f16])).
% 2.19/0.65  fof(f16,plain,(
% 2.19/0.65    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f15])).
% 2.19/0.65  fof(f15,negated_conjecture,(
% 2.19/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.19/0.65    inference(negated_conjecture,[],[f14])).
% 2.19/0.65  fof(f14,conjecture,(
% 2.19/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 2.19/0.65  fof(f87,plain,(
% 2.19/0.65    spl2_7 | ~spl2_5 | ~spl2_6),
% 2.19/0.65    inference(avatar_split_clause,[],[f83,f80,f76,f85])).
% 2.19/0.65  fof(f83,plain,(
% 2.19/0.65    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_5 | ~spl2_6)),
% 2.19/0.65    inference(superposition,[],[f81,f77])).
% 2.19/0.65  fof(f82,plain,(
% 2.19/0.65    spl2_6),
% 2.19/0.65    inference(avatar_split_clause,[],[f52,f80])).
% 2.19/0.65  fof(f52,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.19/0.65    inference(definition_unfolding,[],[f39,f40])).
% 2.19/0.65  fof(f39,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f5])).
% 2.19/0.65  fof(f5,axiom,(
% 2.19/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.19/0.65  fof(f78,plain,(
% 2.19/0.65    spl2_5),
% 2.19/0.65    inference(avatar_split_clause,[],[f51,f76])).
% 2.19/0.65  fof(f51,plain,(
% 2.19/0.65    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.19/0.65    inference(definition_unfolding,[],[f38,f40])).
% 2.19/0.65  fof(f38,plain,(
% 2.19/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.65    inference(cnf_transformation,[],[f6])).
% 2.19/0.65  fof(f6,axiom,(
% 2.19/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.65  fof(f70,plain,(
% 2.19/0.65    spl2_3),
% 2.19/0.65    inference(avatar_split_clause,[],[f35,f67])).
% 2.19/0.65  fof(f35,plain,(
% 2.19/0.65    v2_funct_1(sK1)),
% 2.19/0.65    inference(cnf_transformation,[],[f31])).
% 2.19/0.65  fof(f65,plain,(
% 2.19/0.65    spl2_2),
% 2.19/0.65    inference(avatar_split_clause,[],[f34,f62])).
% 2.19/0.65  fof(f34,plain,(
% 2.19/0.65    v1_funct_1(sK1)),
% 2.19/0.65    inference(cnf_transformation,[],[f31])).
% 2.19/0.65  fof(f60,plain,(
% 2.19/0.65    spl2_1),
% 2.19/0.65    inference(avatar_split_clause,[],[f33,f57])).
% 2.19/0.65  fof(f33,plain,(
% 2.19/0.65    v1_relat_1(sK1)),
% 2.19/0.65    inference(cnf_transformation,[],[f31])).
% 2.19/0.65  % SZS output end Proof for theBenchmark
% 2.19/0.65  % (17172)------------------------------
% 2.19/0.65  % (17172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (17172)Termination reason: Refutation
% 2.19/0.65  
% 2.19/0.65  % (17172)Memory used [KB]: 8699
% 2.19/0.65  % (17172)Time elapsed: 0.220 s
% 2.19/0.65  % (17172)------------------------------
% 2.19/0.65  % (17172)------------------------------
% 2.19/0.65  % (17164)Success in time 0.297 s
%------------------------------------------------------------------------------
