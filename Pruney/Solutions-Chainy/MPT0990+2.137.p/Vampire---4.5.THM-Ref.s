%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:52 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  355 ( 819 expanded)
%              Number of leaves         :   74 ( 345 expanded)
%              Depth                    :   16
%              Number of atoms          : 1596 (3684 expanded)
%              Number of equality atoms :  284 ( 885 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f181,f191,f197,f244,f274,f299,f350,f364,f371,f412,f480,f489,f491,f510,f574,f581,f593,f602,f696,f756,f757,f906,f948,f1012,f1028,f1102,f1155,f1159,f1167,f1216,f1428,f1464,f1465,f1466,f1467,f1470])).

fof(f1470,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1467,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1466,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1465,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | sK1 != k1_relat_1(sK3)
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1464,plain,
    ( ~ spl4_14
    | ~ spl4_37
    | spl4_128 ),
    inference(avatar_contradiction_clause,[],[f1463])).

fof(f1463,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_37
    | spl4_128 ),
    inference(subsumption_resolution,[],[f1462,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1462,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_14
    | ~ spl4_37
    | spl4_128 ),
    inference(forward_demodulation,[],[f1461,f456])).

fof(f456,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1461,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_14
    | spl4_128 ),
    inference(subsumption_resolution,[],[f1460,f190])).

fof(f190,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1460,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_128 ),
    inference(superposition,[],[f1427,f104])).

fof(f104,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1427,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))
    | spl4_128 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f1425,plain,
    ( spl4_128
  <=> r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1428,plain,
    ( ~ spl4_128
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | spl4_91 ),
    inference(avatar_split_clause,[],[f1423,f1136,f465,f188,f157,f1425])).

fof(f157,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f465,plain,
    ( spl4_38
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1136,plain,
    ( spl4_91
  <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1423,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | spl4_91 ),
    inference(subsumption_resolution,[],[f1422,f190])).

fof(f1422,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_38
    | spl4_91 ),
    inference(subsumption_resolution,[],[f1421,f159])).

fof(f159,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f1421,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_38
    | spl4_91 ),
    inference(subsumption_resolution,[],[f1420,f467])).

fof(f467,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f465])).

fof(f1420,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_91 ),
    inference(superposition,[],[f1138,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1138,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1216,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | spl4_83 ),
    inference(avatar_contradiction_clause,[],[f1215])).

fof(f1215,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | spl4_83 ),
    inference(subsumption_resolution,[],[f1214,f190])).

fof(f1214,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_83 ),
    inference(subsumption_resolution,[],[f1211,f159])).

fof(f1211,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_83 ),
    inference(resolution,[],[f1086,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1086,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_83 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1084,plain,
    ( spl4_83
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f1167,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | spl4_80 ),
    inference(avatar_contradiction_clause,[],[f1166])).

fof(f1166,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | spl4_80 ),
    inference(subsumption_resolution,[],[f1165,f190])).

fof(f1165,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_80 ),
    inference(subsumption_resolution,[],[f1162,f159])).

fof(f1162,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_80 ),
    inference(resolution,[],[f1070,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1070,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_80 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f1068,plain,
    ( spl4_80
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1159,plain,
    ( ~ spl4_83
    | spl4_74
    | ~ spl4_91
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1158,f486,f454,f188,f1136,f1025,f1084])).

fof(f1025,plain,
    ( spl4_74
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f486,plain,
    ( spl4_41
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1158,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))
    | sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f1157,f456])).

fof(f1157,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f1156,f97])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1156,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f1108,f190])).

fof(f1108,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_41 ),
    inference(superposition,[],[f101,f488])).

fof(f488,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f486])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f1155,plain,
    ( ~ spl4_83
    | ~ spl4_80
    | ~ spl4_92
    | spl4_93
    | ~ spl4_94
    | ~ spl4_86
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1142,f486,f454,f188,f157,f1099,f1152,f1148,f1144,f1068,f1084])).

fof(f1144,plain,
    ( spl4_92
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f1148,plain,
    ( spl4_93
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1152,plain,
    ( spl4_94
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1099,plain,
    ( spl4_86
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1142,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f1141,f456])).

fof(f1141,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f1140,f190])).

fof(f1140,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f1107,f159])).

fof(f1107,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_41 ),
    inference(superposition,[],[f78,f488])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1102,plain,
    ( ~ spl4_83
    | ~ spl4_84
    | spl4_86
    | ~ spl4_14
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f1097,f477,f188,f1099,f1088,f1084])).

fof(f1088,plain,
    ( spl4_84
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f477,plain,
    ( spl4_40
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1097,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_14
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1096,f97])).

fof(f1096,plain,
    ( k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_14
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1057,f190])).

fof(f1057,plain,
    ( k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(superposition,[],[f101,f479])).

fof(f479,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f477])).

fof(f1028,plain,
    ( ~ spl4_38
    | spl4_73
    | ~ spl4_74
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f1019,f599,f454,f239,f194,f188,f172,f157,f1025,f1021,f465])).

fof(f1021,plain,
    ( spl4_73
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f172,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f194,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f239,plain,
    ( spl4_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f599,plain,
    ( spl4_52
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1019,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1018,f241])).

fof(f241,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f239])).

fof(f1018,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(trivial_inequality_removal,[],[f1017])).

fof(f1017,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1016,f456])).

fof(f1016,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f1015,f190])).

fof(f1015,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f1014,f159])).

fof(f1014,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f1013,f196])).

fof(f196,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1013,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f914,f174])).

fof(f174,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f914,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_52 ),
    inference(superposition,[],[f78,f601])).

fof(f601,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f599])).

fof(f1012,plain,
    ( spl4_38
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1011,f590,f172,f167,f162,f157,f152,f147,f142,f127,f465])).

fof(f127,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f142,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f147,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f152,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f162,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f167,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f590,plain,
    ( spl4_50
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1011,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1010,f159])).

fof(f1010,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1009,f154])).

fof(f154,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1009,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1008,f149])).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1008,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f997,f129])).

fof(f129,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f997,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f989,f87])).

fof(f87,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f989,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(superposition,[],[f432,f592])).

fof(f592,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f590])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f431,f174])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f430,f169])).

fof(f169,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f430,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f429,f164])).

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f429,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f426])).

fof(f426,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f84,f144])).

fof(f144,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f948,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_49 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_49 ),
    inference(subsumption_resolution,[],[f946,f174])).

fof(f946,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_49 ),
    inference(subsumption_resolution,[],[f945,f164])).

fof(f945,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_49 ),
    inference(subsumption_resolution,[],[f944,f159])).

fof(f944,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_49 ),
    inference(subsumption_resolution,[],[f941,f149])).

fof(f941,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_49 ),
    inference(resolution,[],[f588,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f588,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl4_49
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f906,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_51 ),
    inference(avatar_contradiction_clause,[],[f904])).

fof(f904,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f174,f159,f164,f149,f597,f280])).

fof(f280,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f279])).

% (12265)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f279,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f94,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f597,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl4_51
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f757,plain,
    ( sK0 != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f756,plain,
    ( ~ spl4_15
    | ~ spl4_30
    | spl4_59 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_30
    | spl4_59 ),
    inference(subsumption_resolution,[],[f754,f113])).

fof(f754,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_15
    | ~ spl4_30
    | spl4_59 ),
    inference(forward_demodulation,[],[f753,f345])).

fof(f345,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl4_30
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f753,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_15
    | spl4_59 ),
    inference(subsumption_resolution,[],[f752,f196])).

fof(f752,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl4_59 ),
    inference(superposition,[],[f695,f105])).

fof(f105,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f695,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | spl4_59 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl4_59
  <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f696,plain,
    ( ~ spl4_59
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_58 ),
    inference(avatar_split_clause,[],[f691,f664,f194,f172,f132,f693])).

fof(f132,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f664,plain,
    ( spl4_58
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f691,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_58 ),
    inference(subsumption_resolution,[],[f690,f196])).

fof(f690,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | spl4_58 ),
    inference(subsumption_resolution,[],[f689,f174])).

fof(f689,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | spl4_58 ),
    inference(subsumption_resolution,[],[f688,f134])).

fof(f134,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f688,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_58 ),
    inference(superposition,[],[f666,f79])).

fof(f666,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f664])).

fof(f602,plain,
    ( ~ spl4_51
    | spl4_52
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f583,f271,f599,f595])).

fof(f271,plain,
    ( spl4_21
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f583,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_21 ),
    inference(resolution,[],[f261,f273])).

fof(f273,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f271])).

fof(f261,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f88,f182])).

fof(f182,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f593,plain,
    ( ~ spl4_49
    | spl4_50
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f582,f178,f590,f586])).

fof(f178,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f582,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f261,f180])).

fof(f180,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f581,plain,
    ( ~ spl4_15
    | ~ spl4_19
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_19
    | spl4_48 ),
    inference(subsumption_resolution,[],[f579,f113])).

fof(f579,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_15
    | ~ spl4_19
    | spl4_48 ),
    inference(forward_demodulation,[],[f578,f241])).

fof(f578,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl4_15
    | spl4_48 ),
    inference(subsumption_resolution,[],[f577,f196])).

fof(f577,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl4_48 ),
    inference(superposition,[],[f573,f104])).

fof(f573,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl4_48
  <=> r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f574,plain,
    ( ~ spl4_48
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(avatar_split_clause,[],[f569,f347,f194,f172,f132,f571])).

fof(f347,plain,
    ( spl4_31
  <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f569,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(subsumption_resolution,[],[f568,f196])).

fof(f568,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | spl4_31 ),
    inference(subsumption_resolution,[],[f567,f174])).

fof(f567,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | spl4_31 ),
    inference(subsumption_resolution,[],[f566,f134])).

fof(f566,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_31 ),
    inference(superposition,[],[f349,f79])).

fof(f349,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f347])).

fof(f510,plain,
    ( ~ spl4_43
    | spl4_29
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f505,f361,f315,f194,f335,f507])).

fof(f507,plain,
    ( spl4_43
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f335,plain,
    ( spl4_29
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f315,plain,
    ( spl4_24
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f361,plain,
    ( spl4_32
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f505,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f504,f97])).

fof(f504,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f503,f316])).

fof(f316,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f315])).

fof(f503,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f494,f196])).

fof(f494,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_32 ),
    inference(superposition,[],[f101,f363])).

fof(f363,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f361])).

fof(f491,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f490,f409,f147,f454])).

fof(f409,plain,
    ( spl4_34
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f490,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f447,f149])).

fof(f447,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_34 ),
    inference(superposition,[],[f96,f411])).

fof(f411,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f409])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f489,plain,
    ( spl4_41
    | ~ spl4_38
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f484,f409,f157,f152,f147,f127,f465,f486])).

fof(f484,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f483,f159])).

fof(f483,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f482,f154])).

fof(f482,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f481,f149])).

fof(f481,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f448,f129])).

fof(f448,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_34 ),
    inference(trivial_inequality_removal,[],[f446])).

fof(f446,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_34 ),
    inference(superposition,[],[f282,f411])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f75,f92])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f480,plain,
    ( spl4_40
    | ~ spl4_38
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f475,f409,f157,f152,f147,f127,f465,f477])).

fof(f475,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f474,f159])).

fof(f474,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f473,f154])).

fof(f473,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f472,f149])).

fof(f472,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f449,f129])).

fof(f449,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_34 ),
    inference(trivial_inequality_removal,[],[f445])).

fof(f445,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_34 ),
    inference(superposition,[],[f285,f411])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f76,f92])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f412,plain,
    ( spl4_34
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f407,f178,f172,f167,f162,f157,f152,f147,f409])).

fof(f407,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f406,f159])).

fof(f406,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f405,f154])).

fof(f405,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f404,f149])).

fof(f404,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f403,f174])).

fof(f403,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f402,f169])).

fof(f402,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f399,f164])).

fof(f399,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f388,f180])).

fof(f388,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f90,f92])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f371,plain,
    ( ~ spl4_12
    | ~ spl4_15
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_15
    | spl4_24 ),
    inference(subsumption_resolution,[],[f369,f196])).

fof(f369,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_24 ),
    inference(subsumption_resolution,[],[f366,f174])).

fof(f366,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_24 ),
    inference(resolution,[],[f317,f80])).

fof(f317,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f315])).

fof(f364,plain,
    ( spl4_32
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f359,f172,f167,f162,f142,f132,f122,f361])).

fof(f122,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f359,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f358,f174])).

fof(f358,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f357,f169])).

fof(f357,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f356,f164])).

fof(f356,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f355,f134])).

fof(f355,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f354,f124])).

fof(f124,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f354,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f351])).

fof(f351,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f285,f144])).

fof(f350,plain,
    ( ~ spl4_24
    | spl4_30
    | ~ spl4_31
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f341,f296,f239,f194,f347,f343,f315])).

fof(f296,plain,
    ( spl4_22
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f341,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f340,f241])).

fof(f340,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f339,f97])).

fof(f339,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f302,f196])).

fof(f302,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f101,f298])).

fof(f298,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f296])).

fof(f299,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f294,f172,f167,f162,f142,f132,f122,f296])).

fof(f294,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f293,f174])).

fof(f293,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f292,f169])).

fof(f292,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f291,f164])).

fof(f291,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f290,f134])).

fof(f290,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f289,f124])).

fof(f289,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f286])).

fof(f286,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f282,f144])).

fof(f274,plain,
    ( spl4_21
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f269,f178,f172,f162,f157,f147,f271])).

fof(f269,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f268,f174])).

fof(f268,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f267,f164])).

fof(f267,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f266,f159])).

fof(f266,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f263,f149])).

fof(f263,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f180,f95])).

fof(f244,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f243,f162,f142,f239])).

fof(f243,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f236,f164])).

fof(f236,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f144,f96])).

fof(f197,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f192,f162,f194])).

fof(f192,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f184,f100])).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f184,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f99,f164])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f191,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f186,f147,f188])).

fof(f186,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f183,f100])).

fof(f183,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f99,f149])).

fof(f181,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f176,f137,f178])).

fof(f137,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f176,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f139,f92])).

fof(f139,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f175,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f63,f172])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f58,f57])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f170,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f64,f167])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f165,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f65,f162])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f160,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f66,f157])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f155,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f67,f152])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f150,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f68,f147])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f145,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f69,f142])).

fof(f69,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f140,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f70,f137])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f135,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f71,f132])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f130,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f72,f127])).

fof(f72,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f59])).

fof(f125,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f122])).

fof(f73,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f74,f117])).

fof(f117,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.19/0.51  % (12223)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.52  % (12233)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.52  % (12246)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.52  % (12225)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.53  % (12228)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.19/0.53  % (12238)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.53  % (12230)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.53  % (12229)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (12224)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.54  % (12227)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (12231)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.54  % (12239)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (12251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.54  % (12242)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.35/0.54  % (12239)Refutation not found, incomplete strategy% (12239)------------------------------
% 1.35/0.54  % (12239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (12239)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (12239)Memory used [KB]: 10746
% 1.35/0.54  % (12239)Time elapsed: 0.126 s
% 1.35/0.54  % (12239)------------------------------
% 1.35/0.54  % (12239)------------------------------
% 1.35/0.54  % (12250)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.35/0.54  % (12240)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.35/0.54  % (12252)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.54  % (12243)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.55  % (12233)Refutation not found, incomplete strategy% (12233)------------------------------
% 1.35/0.55  % (12233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (12233)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (12233)Memory used [KB]: 11001
% 1.35/0.55  % (12233)Time elapsed: 0.131 s
% 1.35/0.55  % (12233)------------------------------
% 1.35/0.55  % (12233)------------------------------
% 1.35/0.55  % (12226)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.55  % (12249)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (12237)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.55  % (12248)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.55  % (12244)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.55  % (12235)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.55  % (12234)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.55  % (12241)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.56  % (12232)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.56  % (12236)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.56  % (12245)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.56  % (12247)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.57  % (12251)Refutation not found, incomplete strategy% (12251)------------------------------
% 1.35/0.57  % (12251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (12251)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (12251)Memory used [KB]: 11001
% 1.35/0.57  % (12251)Time elapsed: 0.171 s
% 1.35/0.57  % (12251)------------------------------
% 1.35/0.57  % (12251)------------------------------
% 2.04/0.64  % (12244)Refutation found. Thanks to Tanya!
% 2.04/0.64  % SZS status Theorem for theBenchmark
% 2.04/0.64  % SZS output start Proof for theBenchmark
% 2.04/0.64  fof(f1471,plain,(
% 2.04/0.64    $false),
% 2.04/0.64    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f181,f191,f197,f244,f274,f299,f350,f364,f371,f412,f480,f489,f491,f510,f574,f581,f593,f602,f696,f756,f757,f906,f948,f1012,f1028,f1102,f1155,f1159,f1167,f1216,f1428,f1464,f1465,f1466,f1467,f1470])).
% 2.04/0.64  fof(f1470,plain,(
% 2.04/0.64    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 2.04/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.64  fof(f1467,plain,(
% 2.04/0.64    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 2.04/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.64  fof(f1466,plain,(
% 2.04/0.64    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 2.04/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.64  fof(f1465,plain,(
% 2.04/0.64    sK1 != k1_relat_1(k2_funct_1(sK2)) | sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | sK1 != k1_relat_1(sK3) | r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))),
% 2.04/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.64  fof(f1464,plain,(
% 2.04/0.64    ~spl4_14 | ~spl4_37 | spl4_128),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f1463])).
% 2.04/0.64  fof(f1463,plain,(
% 2.04/0.64    $false | (~spl4_14 | ~spl4_37 | spl4_128)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1462,f113])).
% 2.04/0.64  fof(f113,plain,(
% 2.04/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/0.64    inference(equality_resolution,[],[f108])).
% 2.04/0.64  fof(f108,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.04/0.64    inference(cnf_transformation,[],[f62])).
% 2.04/0.64  fof(f62,plain,(
% 2.04/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.64    inference(flattening,[],[f61])).
% 2.04/0.64  fof(f61,plain,(
% 2.04/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.64    inference(nnf_transformation,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.64  fof(f1462,plain,(
% 2.04/0.64    ~r1_tarski(sK0,sK0) | (~spl4_14 | ~spl4_37 | spl4_128)),
% 2.04/0.64    inference(forward_demodulation,[],[f1461,f456])).
% 2.04/0.64  fof(f456,plain,(
% 2.04/0.64    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 2.04/0.64    inference(avatar_component_clause,[],[f454])).
% 2.04/0.64  fof(f454,plain,(
% 2.04/0.64    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.04/0.64  fof(f1461,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k2_relat_1(sK3)) | (~spl4_14 | spl4_128)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1460,f190])).
% 2.04/0.64  fof(f190,plain,(
% 2.04/0.64    v1_relat_1(sK3) | ~spl4_14),
% 2.04/0.64    inference(avatar_component_clause,[],[f188])).
% 2.04/0.64  fof(f188,plain,(
% 2.04/0.64    spl4_14 <=> v1_relat_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.04/0.64  fof(f1460,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_128),
% 2.04/0.64    inference(superposition,[],[f1427,f104])).
% 2.04/0.64  fof(f104,plain,(
% 2.04/0.64    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f55])).
% 2.04/0.64  fof(f55,plain,(
% 2.04/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 2.04/0.64  fof(f1427,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) | spl4_128),
% 2.04/0.64    inference(avatar_component_clause,[],[f1425])).
% 2.04/0.64  fof(f1425,plain,(
% 2.04/0.64    spl4_128 <=> r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).
% 2.04/0.64  fof(f1428,plain,(
% 2.04/0.64    ~spl4_128 | ~spl4_9 | ~spl4_14 | ~spl4_38 | spl4_91),
% 2.04/0.64    inference(avatar_split_clause,[],[f1423,f1136,f465,f188,f157,f1425])).
% 2.04/0.64  fof(f157,plain,(
% 2.04/0.64    spl4_9 <=> v1_funct_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.04/0.64  fof(f465,plain,(
% 2.04/0.64    spl4_38 <=> v2_funct_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.04/0.64  fof(f1136,plain,(
% 2.04/0.64    spl4_91 <=> r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 2.04/0.64  fof(f1423,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) | (~spl4_9 | ~spl4_14 | ~spl4_38 | spl4_91)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1422,f190])).
% 2.04/0.64  fof(f1422,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_38 | spl4_91)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1421,f159])).
% 2.04/0.64  fof(f159,plain,(
% 2.04/0.64    v1_funct_1(sK3) | ~spl4_9),
% 2.04/0.64    inference(avatar_component_clause,[],[f157])).
% 2.04/0.64  fof(f1421,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_38 | spl4_91)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1420,f467])).
% 2.04/0.64  fof(f467,plain,(
% 2.04/0.64    v2_funct_1(sK3) | ~spl4_38),
% 2.04/0.64    inference(avatar_component_clause,[],[f465])).
% 2.04/0.64  fof(f1420,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k4_relat_1(sK3))) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_91),
% 2.04/0.64    inference(superposition,[],[f1138,f79])).
% 2.04/0.64  fof(f79,plain,(
% 2.04/0.64    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f36])).
% 2.04/0.64  fof(f36,plain,(
% 2.04/0.64    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(flattening,[],[f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f10])).
% 2.04/0.64  fof(f10,axiom,(
% 2.04/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.04/0.64  fof(f1138,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | spl4_91),
% 2.04/0.64    inference(avatar_component_clause,[],[f1136])).
% 2.04/0.64  fof(f1216,plain,(
% 2.04/0.64    ~spl4_9 | ~spl4_14 | spl4_83),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f1215])).
% 2.04/0.64  fof(f1215,plain,(
% 2.04/0.64    $false | (~spl4_9 | ~spl4_14 | spl4_83)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1214,f190])).
% 2.04/0.64  fof(f1214,plain,(
% 2.04/0.64    ~v1_relat_1(sK3) | (~spl4_9 | spl4_83)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1211,f159])).
% 2.04/0.64  fof(f1211,plain,(
% 2.04/0.64    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_83),
% 2.04/0.64    inference(resolution,[],[f1086,f80])).
% 2.04/0.64  fof(f80,plain,(
% 2.04/0.64    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(flattening,[],[f37])).
% 2.04/0.64  fof(f37,plain,(
% 2.04/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f11])).
% 2.04/0.64  fof(f11,axiom,(
% 2.04/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.04/0.64  fof(f1086,plain,(
% 2.04/0.64    ~v1_relat_1(k2_funct_1(sK3)) | spl4_83),
% 2.04/0.64    inference(avatar_component_clause,[],[f1084])).
% 2.04/0.64  fof(f1084,plain,(
% 2.04/0.64    spl4_83 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 2.04/0.64  fof(f1167,plain,(
% 2.04/0.64    ~spl4_9 | ~spl4_14 | spl4_80),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f1166])).
% 2.04/0.64  fof(f1166,plain,(
% 2.04/0.64    $false | (~spl4_9 | ~spl4_14 | spl4_80)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1165,f190])).
% 2.04/0.64  fof(f1165,plain,(
% 2.04/0.64    ~v1_relat_1(sK3) | (~spl4_9 | spl4_80)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1162,f159])).
% 2.04/0.64  fof(f1162,plain,(
% 2.04/0.64    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_80),
% 2.04/0.64    inference(resolution,[],[f1070,f81])).
% 2.04/0.64  fof(f81,plain,(
% 2.04/0.64    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f38])).
% 2.04/0.64  fof(f1070,plain,(
% 2.04/0.64    ~v1_funct_1(k2_funct_1(sK3)) | spl4_80),
% 2.04/0.64    inference(avatar_component_clause,[],[f1068])).
% 2.04/0.64  fof(f1068,plain,(
% 2.04/0.64    spl4_80 <=> v1_funct_1(k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 2.04/0.64  fof(f1159,plain,(
% 2.04/0.64    ~spl4_83 | spl4_74 | ~spl4_91 | ~spl4_14 | ~spl4_37 | ~spl4_41),
% 2.04/0.64    inference(avatar_split_clause,[],[f1158,f486,f454,f188,f1136,f1025,f1084])).
% 2.04/0.64  fof(f1025,plain,(
% 2.04/0.64    spl4_74 <=> sK1 = k1_relat_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 2.04/0.64  fof(f486,plain,(
% 2.04/0.64    spl4_41 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.04/0.64  fof(f1158,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k1_relat_1(k2_funct_1(sK3))) | sK1 = k1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_14 | ~spl4_37 | ~spl4_41)),
% 2.04/0.64    inference(forward_demodulation,[],[f1157,f456])).
% 2.04/0.64  fof(f1157,plain,(
% 2.04/0.64    sK1 = k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_14 | ~spl4_41)),
% 2.04/0.64    inference(forward_demodulation,[],[f1156,f97])).
% 2.04/0.64  fof(f97,plain,(
% 2.04/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f9])).
% 2.04/0.64  fof(f9,axiom,(
% 2.04/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.04/0.64  fof(f1156,plain,(
% 2.04/0.64    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_14 | ~spl4_41)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1108,f190])).
% 2.04/0.64  fof(f1108,plain,(
% 2.04/0.64    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_41),
% 2.04/0.64    inference(superposition,[],[f101,f488])).
% 2.04/0.64  fof(f488,plain,(
% 2.04/0.64    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_41),
% 2.04/0.64    inference(avatar_component_clause,[],[f486])).
% 2.04/0.64  fof(f101,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f52])).
% 2.04/0.64  fof(f52,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(flattening,[],[f51])).
% 2.04/0.64  fof(f51,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 2.04/0.64  fof(f1155,plain,(
% 2.04/0.64    ~spl4_83 | ~spl4_80 | ~spl4_92 | spl4_93 | ~spl4_94 | ~spl4_86 | ~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_41),
% 2.04/0.64    inference(avatar_split_clause,[],[f1142,f486,f454,f188,f157,f1099,f1152,f1148,f1144,f1068,f1084])).
% 2.04/0.64  fof(f1144,plain,(
% 2.04/0.64    spl4_92 <=> v2_funct_1(k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 2.04/0.64  fof(f1148,plain,(
% 2.04/0.64    spl4_93 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 2.04/0.64  fof(f1152,plain,(
% 2.04/0.64    spl4_94 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 2.04/0.64  fof(f1099,plain,(
% 2.04/0.64    spl4_86 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 2.04/0.64  fof(f1142,plain,(
% 2.04/0.64    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_41)),
% 2.04/0.64    inference(forward_demodulation,[],[f1141,f456])).
% 2.04/0.64  fof(f1141,plain,(
% 2.04/0.64    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_41)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1140,f190])).
% 2.04/0.64  fof(f1140,plain,(
% 2.04/0.64    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_41)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1107,f159])).
% 2.04/0.64  fof(f1107,plain,(
% 2.04/0.64    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_41),
% 2.04/0.64    inference(superposition,[],[f78,f488])).
% 2.04/0.64  fof(f78,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f34])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(flattening,[],[f33])).
% 2.04/0.64  fof(f33,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f14])).
% 2.04/0.64  fof(f14,axiom,(
% 2.04/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.04/0.64  fof(f1102,plain,(
% 2.04/0.64    ~spl4_83 | ~spl4_84 | spl4_86 | ~spl4_14 | ~spl4_40),
% 2.04/0.64    inference(avatar_split_clause,[],[f1097,f477,f188,f1099,f1088,f1084])).
% 2.04/0.64  fof(f1088,plain,(
% 2.04/0.64    spl4_84 <=> r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 2.04/0.64  fof(f477,plain,(
% 2.04/0.64    spl4_40 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.04/0.64  fof(f1097,plain,(
% 2.04/0.64    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_14 | ~spl4_40)),
% 2.04/0.64    inference(forward_demodulation,[],[f1096,f97])).
% 2.04/0.64  fof(f1096,plain,(
% 2.04/0.64    k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_14 | ~spl4_40)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1057,f190])).
% 2.04/0.64  fof(f1057,plain,(
% 2.04/0.64    k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_40),
% 2.04/0.64    inference(superposition,[],[f101,f479])).
% 2.04/0.64  fof(f479,plain,(
% 2.04/0.64    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_40),
% 2.04/0.64    inference(avatar_component_clause,[],[f477])).
% 2.04/0.64  fof(f1028,plain,(
% 2.04/0.64    ~spl4_38 | spl4_73 | ~spl4_74 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_19 | ~spl4_37 | ~spl4_52),
% 2.04/0.64    inference(avatar_split_clause,[],[f1019,f599,f454,f239,f194,f188,f172,f157,f1025,f1021,f465])).
% 2.04/0.64  fof(f1021,plain,(
% 2.04/0.64    spl4_73 <=> sK2 = k2_funct_1(sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 2.04/0.64  fof(f172,plain,(
% 2.04/0.64    spl4_12 <=> v1_funct_1(sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.04/0.64  fof(f194,plain,(
% 2.04/0.64    spl4_15 <=> v1_relat_1(sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.04/0.64  fof(f239,plain,(
% 2.04/0.64    spl4_19 <=> sK1 = k2_relat_1(sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.04/0.64  fof(f599,plain,(
% 2.04/0.64    spl4_52 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.04/0.64  fof(f1019,plain,(
% 2.04/0.64    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_19 | ~spl4_37 | ~spl4_52)),
% 2.04/0.64    inference(forward_demodulation,[],[f1018,f241])).
% 2.04/0.64  fof(f241,plain,(
% 2.04/0.64    sK1 = k2_relat_1(sK2) | ~spl4_19),
% 2.04/0.64    inference(avatar_component_clause,[],[f239])).
% 2.04/0.64  fof(f1018,plain,(
% 2.04/0.64    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_52)),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f1017])).
% 2.04/0.64  fof(f1017,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_52)),
% 2.04/0.64    inference(forward_demodulation,[],[f1016,f456])).
% 2.04/0.64  fof(f1016,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_52)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1015,f190])).
% 2.04/0.64  fof(f1015,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_52)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1014,f159])).
% 2.04/0.64  fof(f1014,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_52)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1013,f196])).
% 2.04/0.64  fof(f196,plain,(
% 2.04/0.64    v1_relat_1(sK2) | ~spl4_15),
% 2.04/0.64    inference(avatar_component_clause,[],[f194])).
% 2.04/0.64  fof(f1013,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_52)),
% 2.04/0.64    inference(subsumption_resolution,[],[f914,f174])).
% 2.04/0.64  fof(f174,plain,(
% 2.04/0.64    v1_funct_1(sK2) | ~spl4_12),
% 2.04/0.64    inference(avatar_component_clause,[],[f172])).
% 2.04/0.64  fof(f914,plain,(
% 2.04/0.64    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_52),
% 2.04/0.64    inference(superposition,[],[f78,f601])).
% 2.04/0.64  fof(f601,plain,(
% 2.04/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_52),
% 2.04/0.64    inference(avatar_component_clause,[],[f599])).
% 2.04/0.64  fof(f1012,plain,(
% 2.04/0.64    spl4_38 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50),
% 2.04/0.64    inference(avatar_split_clause,[],[f1011,f590,f172,f167,f162,f157,f152,f147,f142,f127,f465])).
% 2.04/0.64  fof(f127,plain,(
% 2.04/0.64    spl4_3 <=> k1_xboole_0 = sK0),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.04/0.64  fof(f142,plain,(
% 2.04/0.64    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.04/0.64  fof(f147,plain,(
% 2.04/0.64    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.04/0.64  fof(f152,plain,(
% 2.04/0.64    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.04/0.64  fof(f162,plain,(
% 2.04/0.64    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.04/0.64  fof(f167,plain,(
% 2.04/0.64    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.04/0.64  fof(f590,plain,(
% 2.04/0.64    spl4_50 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 2.04/0.64  fof(f1011,plain,(
% 2.04/0.64    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1010,f159])).
% 2.04/0.64  fof(f1010,plain,(
% 2.04/0.64    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1009,f154])).
% 2.04/0.64  fof(f154,plain,(
% 2.04/0.64    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.04/0.64    inference(avatar_component_clause,[],[f152])).
% 2.04/0.64  fof(f1009,plain,(
% 2.04/0.64    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(subsumption_resolution,[],[f1008,f149])).
% 2.04/0.64  fof(f149,plain,(
% 2.04/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.04/0.64    inference(avatar_component_clause,[],[f147])).
% 2.04/0.64  fof(f1008,plain,(
% 2.04/0.64    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(subsumption_resolution,[],[f997,f129])).
% 2.04/0.64  fof(f129,plain,(
% 2.04/0.64    k1_xboole_0 != sK0 | spl4_3),
% 2.04/0.64    inference(avatar_component_clause,[],[f127])).
% 2.04/0.64  fof(f997,plain,(
% 2.04/0.64    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(subsumption_resolution,[],[f989,f87])).
% 2.04/0.64  fof(f87,plain,(
% 2.04/0.64    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.04/0.64  fof(f989,plain,(
% 2.04/0.64    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_50)),
% 2.04/0.64    inference(superposition,[],[f432,f592])).
% 2.04/0.64  fof(f592,plain,(
% 2.04/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_50),
% 2.04/0.64    inference(avatar_component_clause,[],[f590])).
% 2.04/0.64  fof(f432,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.04/0.64    inference(subsumption_resolution,[],[f431,f174])).
% 2.04/0.64  fof(f431,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.04/0.64    inference(subsumption_resolution,[],[f430,f169])).
% 2.04/0.64  fof(f169,plain,(
% 2.04/0.64    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.04/0.64    inference(avatar_component_clause,[],[f167])).
% 2.04/0.64  fof(f430,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 2.04/0.64    inference(subsumption_resolution,[],[f429,f164])).
% 2.04/0.64  fof(f164,plain,(
% 2.04/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.04/0.64    inference(avatar_component_clause,[],[f162])).
% 2.04/0.64  fof(f429,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 2.04/0.64    inference(trivial_inequality_removal,[],[f426])).
% 2.04/0.64  fof(f426,plain,(
% 2.04/0.64    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 2.04/0.64    inference(superposition,[],[f84,f144])).
% 2.04/0.64  fof(f144,plain,(
% 2.04/0.64    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.04/0.64    inference(avatar_component_clause,[],[f142])).
% 2.04/0.64  fof(f84,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f40])).
% 2.04/0.64  fof(f40,plain,(
% 2.04/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.04/0.64    inference(flattening,[],[f39])).
% 2.04/0.64  fof(f39,plain,(
% 2.04/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.04/0.64    inference(ennf_transformation,[],[f22])).
% 2.04/0.64  fof(f22,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.04/0.64  fof(f948,plain,(
% 2.04/0.64    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_49),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f947])).
% 2.04/0.64  fof(f947,plain,(
% 2.04/0.64    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_49)),
% 2.04/0.64    inference(subsumption_resolution,[],[f946,f174])).
% 2.04/0.64  fof(f946,plain,(
% 2.04/0.64    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_49)),
% 2.04/0.64    inference(subsumption_resolution,[],[f945,f164])).
% 2.04/0.64  fof(f945,plain,(
% 2.04/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_49)),
% 2.04/0.64    inference(subsumption_resolution,[],[f944,f159])).
% 2.04/0.64  fof(f944,plain,(
% 2.04/0.64    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_49)),
% 2.04/0.64    inference(subsumption_resolution,[],[f941,f149])).
% 2.04/0.64  fof(f941,plain,(
% 2.04/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_49),
% 2.04/0.64    inference(resolution,[],[f588,f94])).
% 2.04/0.64  fof(f94,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f46])).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.04/0.64    inference(flattening,[],[f45])).
% 2.04/0.64  fof(f45,plain,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.04/0.64    inference(ennf_transformation,[],[f17])).
% 2.04/0.64  fof(f17,axiom,(
% 2.04/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.04/0.64  fof(f588,plain,(
% 2.04/0.64    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_49),
% 2.04/0.64    inference(avatar_component_clause,[],[f586])).
% 2.04/0.64  fof(f586,plain,(
% 2.04/0.64    spl4_49 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.04/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.04/0.64  fof(f906,plain,(
% 2.04/0.64    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_51),
% 2.04/0.64    inference(avatar_contradiction_clause,[],[f904])).
% 2.04/0.64  fof(f904,plain,(
% 2.04/0.64    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_51)),
% 2.04/0.64    inference(unit_resulting_resolution,[],[f174,f159,f164,f149,f597,f280])).
% 2.04/0.64  fof(f280,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.04/0.64    inference(duplicate_literal_removal,[],[f279])).
% 2.04/0.66  % (12265)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.66  fof(f279,plain,(
% 2.04/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.04/0.66    inference(superposition,[],[f94,f95])).
% 2.04/0.66  fof(f95,plain,(
% 2.04/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f48])).
% 2.04/0.66  fof(f48,plain,(
% 2.04/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.04/0.66    inference(flattening,[],[f47])).
% 2.04/0.66  fof(f47,plain,(
% 2.04/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.04/0.66    inference(ennf_transformation,[],[f19])).
% 2.04/0.66  fof(f19,axiom,(
% 2.04/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.04/0.66  fof(f597,plain,(
% 2.04/0.66    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_51),
% 2.04/0.66    inference(avatar_component_clause,[],[f595])).
% 2.04/0.66  fof(f595,plain,(
% 2.04/0.66    spl4_51 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.04/0.66  fof(f757,plain,(
% 2.04/0.66    sK0 != k1_relat_1(sK2) | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 2.04/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.66  fof(f756,plain,(
% 2.04/0.66    ~spl4_15 | ~spl4_30 | spl4_59),
% 2.04/0.66    inference(avatar_contradiction_clause,[],[f755])).
% 2.04/0.66  fof(f755,plain,(
% 2.04/0.66    $false | (~spl4_15 | ~spl4_30 | spl4_59)),
% 2.04/0.66    inference(subsumption_resolution,[],[f754,f113])).
% 2.04/0.66  fof(f754,plain,(
% 2.04/0.66    ~r1_tarski(sK0,sK0) | (~spl4_15 | ~spl4_30 | spl4_59)),
% 2.04/0.66    inference(forward_demodulation,[],[f753,f345])).
% 2.04/0.66  fof(f345,plain,(
% 2.04/0.66    sK0 = k1_relat_1(sK2) | ~spl4_30),
% 2.04/0.66    inference(avatar_component_clause,[],[f343])).
% 2.04/0.66  fof(f343,plain,(
% 2.04/0.66    spl4_30 <=> sK0 = k1_relat_1(sK2)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.04/0.66  fof(f753,plain,(
% 2.04/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | (~spl4_15 | spl4_59)),
% 2.04/0.66    inference(subsumption_resolution,[],[f752,f196])).
% 2.04/0.66  fof(f752,plain,(
% 2.04/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | spl4_59),
% 2.04/0.66    inference(superposition,[],[f695,f105])).
% 2.04/0.66  fof(f105,plain,(
% 2.04/0.66    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f55])).
% 2.04/0.66  fof(f695,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | spl4_59),
% 2.04/0.66    inference(avatar_component_clause,[],[f693])).
% 2.04/0.66  fof(f693,plain,(
% 2.04/0.66    spl4_59 <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.04/0.66  fof(f696,plain,(
% 2.04/0.66    ~spl4_59 | ~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_58),
% 2.04/0.66    inference(avatar_split_clause,[],[f691,f664,f194,f172,f132,f693])).
% 2.04/0.66  fof(f132,plain,(
% 2.04/0.66    spl4_4 <=> v2_funct_1(sK2)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.04/0.66  fof(f664,plain,(
% 2.04/0.66    spl4_58 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.04/0.66  fof(f691,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | (~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_58)),
% 2.04/0.66    inference(subsumption_resolution,[],[f690,f196])).
% 2.04/0.66  fof(f690,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | spl4_58)),
% 2.04/0.66    inference(subsumption_resolution,[],[f689,f174])).
% 2.04/0.66  fof(f689,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | spl4_58)),
% 2.04/0.66    inference(subsumption_resolution,[],[f688,f134])).
% 2.04/0.66  fof(f134,plain,(
% 2.04/0.66    v2_funct_1(sK2) | ~spl4_4),
% 2.04/0.66    inference(avatar_component_clause,[],[f132])).
% 2.04/0.66  fof(f688,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_58),
% 2.04/0.66    inference(superposition,[],[f666,f79])).
% 2.04/0.66  fof(f666,plain,(
% 2.04/0.66    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl4_58),
% 2.04/0.66    inference(avatar_component_clause,[],[f664])).
% 2.04/0.66  fof(f602,plain,(
% 2.04/0.66    ~spl4_51 | spl4_52 | ~spl4_21),
% 2.04/0.66    inference(avatar_split_clause,[],[f583,f271,f599,f595])).
% 2.04/0.66  fof(f271,plain,(
% 2.04/0.66    spl4_21 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.04/0.66  fof(f583,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_21),
% 2.04/0.66    inference(resolution,[],[f261,f273])).
% 2.04/0.66  fof(f273,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_21),
% 2.04/0.66    inference(avatar_component_clause,[],[f271])).
% 2.04/0.66  fof(f261,plain,(
% 2.04/0.66    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.04/0.66    inference(resolution,[],[f88,f182])).
% 2.04/0.66  fof(f182,plain,(
% 2.04/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f91,f92])).
% 2.04/0.66  fof(f92,plain,(
% 2.04/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f20])).
% 2.04/0.66  fof(f20,axiom,(
% 2.04/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.04/0.66  fof(f91,plain,(
% 2.04/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f26])).
% 2.04/0.66  fof(f26,plain,(
% 2.04/0.66    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.04/0.66    inference(pure_predicate_removal,[],[f18])).
% 2.04/0.66  fof(f18,axiom,(
% 2.04/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.04/0.66  fof(f88,plain,(
% 2.04/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f60])).
% 2.04/0.66  fof(f60,plain,(
% 2.04/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.66    inference(nnf_transformation,[],[f42])).
% 2.04/0.66  fof(f42,plain,(
% 2.04/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.66    inference(flattening,[],[f41])).
% 2.04/0.66  fof(f41,plain,(
% 2.04/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.04/0.66    inference(ennf_transformation,[],[f16])).
% 2.04/0.66  fof(f16,axiom,(
% 2.04/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.04/0.66  fof(f593,plain,(
% 2.04/0.66    ~spl4_49 | spl4_50 | ~spl4_13),
% 2.04/0.66    inference(avatar_split_clause,[],[f582,f178,f590,f586])).
% 2.04/0.66  fof(f178,plain,(
% 2.04/0.66    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.04/0.66  fof(f582,plain,(
% 2.04/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 2.04/0.66    inference(resolution,[],[f261,f180])).
% 2.04/0.66  fof(f180,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.04/0.66    inference(avatar_component_clause,[],[f178])).
% 2.04/0.66  fof(f581,plain,(
% 2.04/0.66    ~spl4_15 | ~spl4_19 | spl4_48),
% 2.04/0.66    inference(avatar_contradiction_clause,[],[f580])).
% 2.04/0.66  fof(f580,plain,(
% 2.04/0.66    $false | (~spl4_15 | ~spl4_19 | spl4_48)),
% 2.04/0.66    inference(subsumption_resolution,[],[f579,f113])).
% 2.04/0.66  fof(f579,plain,(
% 2.04/0.66    ~r1_tarski(sK1,sK1) | (~spl4_15 | ~spl4_19 | spl4_48)),
% 2.04/0.66    inference(forward_demodulation,[],[f578,f241])).
% 2.04/0.66  fof(f578,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k2_relat_1(sK2)) | (~spl4_15 | spl4_48)),
% 2.04/0.66    inference(subsumption_resolution,[],[f577,f196])).
% 2.04/0.66  fof(f577,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | spl4_48),
% 2.04/0.66    inference(superposition,[],[f573,f104])).
% 2.04/0.66  fof(f573,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | spl4_48),
% 2.04/0.66    inference(avatar_component_clause,[],[f571])).
% 2.04/0.66  fof(f571,plain,(
% 2.04/0.66    spl4_48 <=> r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.04/0.66  fof(f574,plain,(
% 2.04/0.66    ~spl4_48 | ~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_31),
% 2.04/0.66    inference(avatar_split_clause,[],[f569,f347,f194,f172,f132,f571])).
% 2.04/0.66  fof(f347,plain,(
% 2.04/0.66    spl4_31 <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.04/0.66  fof(f569,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | (~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_31)),
% 2.04/0.66    inference(subsumption_resolution,[],[f568,f196])).
% 2.04/0.66  fof(f568,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | spl4_31)),
% 2.04/0.66    inference(subsumption_resolution,[],[f567,f174])).
% 2.04/0.66  fof(f567,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | spl4_31)),
% 2.04/0.66    inference(subsumption_resolution,[],[f566,f134])).
% 2.04/0.66  fof(f566,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_31),
% 2.04/0.66    inference(superposition,[],[f349,f79])).
% 2.04/0.66  fof(f349,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | spl4_31),
% 2.04/0.66    inference(avatar_component_clause,[],[f347])).
% 2.04/0.66  fof(f510,plain,(
% 2.04/0.66    ~spl4_43 | spl4_29 | ~spl4_15 | ~spl4_24 | ~spl4_32),
% 2.04/0.66    inference(avatar_split_clause,[],[f505,f361,f315,f194,f335,f507])).
% 2.04/0.66  fof(f507,plain,(
% 2.04/0.66    spl4_43 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.04/0.66  fof(f335,plain,(
% 2.04/0.66    spl4_29 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.04/0.66  fof(f315,plain,(
% 2.04/0.66    spl4_24 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.04/0.66  fof(f361,plain,(
% 2.04/0.66    spl4_32 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.04/0.66  fof(f505,plain,(
% 2.04/0.66    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl4_15 | ~spl4_24 | ~spl4_32)),
% 2.04/0.66    inference(forward_demodulation,[],[f504,f97])).
% 2.04/0.66  fof(f504,plain,(
% 2.04/0.66    k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl4_15 | ~spl4_24 | ~spl4_32)),
% 2.04/0.66    inference(subsumption_resolution,[],[f503,f316])).
% 2.04/0.66  fof(f316,plain,(
% 2.04/0.66    v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 2.04/0.66    inference(avatar_component_clause,[],[f315])).
% 2.04/0.66  fof(f503,plain,(
% 2.04/0.66    k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_32)),
% 2.04/0.66    inference(subsumption_resolution,[],[f494,f196])).
% 2.04/0.66  fof(f494,plain,(
% 2.04/0.66    k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_32),
% 2.04/0.66    inference(superposition,[],[f101,f363])).
% 2.04/0.66  fof(f363,plain,(
% 2.04/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_32),
% 2.04/0.66    inference(avatar_component_clause,[],[f361])).
% 2.04/0.66  fof(f491,plain,(
% 2.04/0.66    spl4_37 | ~spl4_7 | ~spl4_34),
% 2.04/0.66    inference(avatar_split_clause,[],[f490,f409,f147,f454])).
% 2.04/0.66  fof(f409,plain,(
% 2.04/0.66    spl4_34 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.04/0.66  fof(f490,plain,(
% 2.04/0.66    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f447,f149])).
% 2.04/0.66  fof(f447,plain,(
% 2.04/0.66    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_34),
% 2.04/0.66    inference(superposition,[],[f96,f411])).
% 2.04/0.66  fof(f411,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_34),
% 2.04/0.66    inference(avatar_component_clause,[],[f409])).
% 2.04/0.66  fof(f96,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f49])).
% 2.04/0.66  fof(f49,plain,(
% 2.04/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.66    inference(ennf_transformation,[],[f15])).
% 2.04/0.66  fof(f15,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.04/0.66  fof(f489,plain,(
% 2.04/0.66    spl4_41 | ~spl4_38 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_34),
% 2.04/0.66    inference(avatar_split_clause,[],[f484,f409,f157,f152,f147,f127,f465,f486])).
% 2.04/0.66  fof(f484,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f483,f159])).
% 2.04/0.66  fof(f483,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f482,f154])).
% 2.04/0.66  fof(f482,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f481,f149])).
% 2.04/0.66  fof(f481,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f448,f129])).
% 2.04/0.66  fof(f448,plain,(
% 2.04/0.66    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_34),
% 2.04/0.66    inference(trivial_inequality_removal,[],[f446])).
% 2.04/0.66  fof(f446,plain,(
% 2.04/0.66    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_34),
% 2.04/0.66    inference(superposition,[],[f282,f411])).
% 2.04/0.66  fof(f282,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f75,f92])).
% 2.04/0.66  fof(f75,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f30])).
% 2.04/0.66  fof(f30,plain,(
% 2.04/0.66    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.04/0.66    inference(flattening,[],[f29])).
% 2.04/0.66  fof(f29,plain,(
% 2.04/0.66    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.04/0.66    inference(ennf_transformation,[],[f23])).
% 2.04/0.66  fof(f23,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.04/0.66  fof(f480,plain,(
% 2.04/0.66    spl4_40 | ~spl4_38 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_34),
% 2.04/0.66    inference(avatar_split_clause,[],[f475,f409,f157,f152,f147,f127,f465,f477])).
% 2.04/0.66  fof(f475,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f474,f159])).
% 2.04/0.66  fof(f474,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f473,f154])).
% 2.04/0.66  fof(f473,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f472,f149])).
% 2.04/0.66  fof(f472,plain,(
% 2.04/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_34)),
% 2.04/0.66    inference(subsumption_resolution,[],[f449,f129])).
% 2.04/0.66  fof(f449,plain,(
% 2.04/0.66    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_34),
% 2.04/0.66    inference(trivial_inequality_removal,[],[f445])).
% 2.04/0.66  fof(f445,plain,(
% 2.04/0.66    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_34),
% 2.04/0.66    inference(superposition,[],[f285,f411])).
% 2.04/0.66  fof(f285,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f76,f92])).
% 2.04/0.66  fof(f76,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f30])).
% 2.04/0.66  fof(f412,plain,(
% 2.04/0.66    spl4_34 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 2.04/0.66    inference(avatar_split_clause,[],[f407,f178,f172,f167,f162,f157,f152,f147,f409])).
% 2.04/0.66  fof(f407,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f406,f159])).
% 2.04/0.66  fof(f406,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f405,f154])).
% 2.04/0.66  fof(f405,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f404,f149])).
% 2.04/0.66  fof(f404,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f403,f174])).
% 2.04/0.66  fof(f403,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f402,f169])).
% 2.04/0.66  fof(f402,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f399,f164])).
% 2.04/0.66  fof(f399,plain,(
% 2.04/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 2.04/0.66    inference(resolution,[],[f388,f180])).
% 2.04/0.66  fof(f388,plain,(
% 2.04/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f90,f92])).
% 2.04/0.66  fof(f90,plain,(
% 2.04/0.66    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f44])).
% 2.04/0.66  fof(f44,plain,(
% 2.04/0.66    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.04/0.66    inference(flattening,[],[f43])).
% 2.04/0.66  fof(f43,plain,(
% 2.04/0.66    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.04/0.66    inference(ennf_transformation,[],[f21])).
% 2.04/0.66  fof(f21,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.04/0.66  fof(f371,plain,(
% 2.04/0.66    ~spl4_12 | ~spl4_15 | spl4_24),
% 2.04/0.66    inference(avatar_contradiction_clause,[],[f370])).
% 2.04/0.66  fof(f370,plain,(
% 2.04/0.66    $false | (~spl4_12 | ~spl4_15 | spl4_24)),
% 2.04/0.66    inference(subsumption_resolution,[],[f369,f196])).
% 2.04/0.66  fof(f369,plain,(
% 2.04/0.66    ~v1_relat_1(sK2) | (~spl4_12 | spl4_24)),
% 2.04/0.66    inference(subsumption_resolution,[],[f366,f174])).
% 2.04/0.66  fof(f366,plain,(
% 2.04/0.66    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_24),
% 2.04/0.66    inference(resolution,[],[f317,f80])).
% 2.04/0.66  fof(f317,plain,(
% 2.04/0.66    ~v1_relat_1(k2_funct_1(sK2)) | spl4_24),
% 2.04/0.66    inference(avatar_component_clause,[],[f315])).
% 2.04/0.66  fof(f364,plain,(
% 2.04/0.66    spl4_32 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.04/0.66    inference(avatar_split_clause,[],[f359,f172,f167,f162,f142,f132,f122,f361])).
% 2.04/0.66  fof(f122,plain,(
% 2.04/0.66    spl4_2 <=> k1_xboole_0 = sK1),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.04/0.66  fof(f359,plain,(
% 2.04/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.04/0.66    inference(subsumption_resolution,[],[f358,f174])).
% 2.04/0.66  fof(f358,plain,(
% 2.04/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.04/0.66    inference(subsumption_resolution,[],[f357,f169])).
% 2.04/0.66  fof(f357,plain,(
% 2.04/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.04/0.66    inference(subsumption_resolution,[],[f356,f164])).
% 2.04/0.66  fof(f356,plain,(
% 2.04/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.04/0.66    inference(subsumption_resolution,[],[f355,f134])).
% 2.04/0.66  fof(f355,plain,(
% 2.04/0.66    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.04/0.66    inference(subsumption_resolution,[],[f354,f124])).
% 2.04/0.66  fof(f124,plain,(
% 2.04/0.66    k1_xboole_0 != sK1 | spl4_2),
% 2.04/0.66    inference(avatar_component_clause,[],[f122])).
% 2.04/0.66  fof(f354,plain,(
% 2.04/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.04/0.66    inference(trivial_inequality_removal,[],[f351])).
% 2.04/0.66  fof(f351,plain,(
% 2.04/0.66    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.04/0.66    inference(superposition,[],[f285,f144])).
% 2.04/0.66  fof(f350,plain,(
% 2.04/0.66    ~spl4_24 | spl4_30 | ~spl4_31 | ~spl4_15 | ~spl4_19 | ~spl4_22),
% 2.04/0.66    inference(avatar_split_clause,[],[f341,f296,f239,f194,f347,f343,f315])).
% 2.04/0.66  fof(f296,plain,(
% 2.04/0.66    spl4_22 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.04/0.66  fof(f341,plain,(
% 2.04/0.66    ~r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | sK0 = k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_19 | ~spl4_22)),
% 2.04/0.66    inference(forward_demodulation,[],[f340,f241])).
% 2.04/0.66  fof(f340,plain,(
% 2.04/0.66    sK0 = k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_22)),
% 2.04/0.66    inference(forward_demodulation,[],[f339,f97])).
% 2.04/0.66  fof(f339,plain,(
% 2.04/0.66    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_22)),
% 2.04/0.66    inference(subsumption_resolution,[],[f302,f196])).
% 2.04/0.66  fof(f302,plain,(
% 2.04/0.66    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_22),
% 2.04/0.66    inference(superposition,[],[f101,f298])).
% 2.04/0.66  fof(f298,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_22),
% 2.04/0.66    inference(avatar_component_clause,[],[f296])).
% 2.04/0.66  fof(f299,plain,(
% 2.04/0.66    spl4_22 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.04/0.66    inference(avatar_split_clause,[],[f294,f172,f167,f162,f142,f132,f122,f296])).
% 2.04/0.66  fof(f294,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.04/0.66    inference(subsumption_resolution,[],[f293,f174])).
% 2.04/0.66  fof(f293,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.04/0.66    inference(subsumption_resolution,[],[f292,f169])).
% 2.04/0.66  fof(f292,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.04/0.66    inference(subsumption_resolution,[],[f291,f164])).
% 2.04/0.66  fof(f291,plain,(
% 2.04/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.04/0.66    inference(subsumption_resolution,[],[f290,f134])).
% 2.04/0.66  fof(f290,plain,(
% 2.04/0.66    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.04/0.66    inference(subsumption_resolution,[],[f289,f124])).
% 2.04/0.66  fof(f289,plain,(
% 2.04/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.04/0.66    inference(trivial_inequality_removal,[],[f286])).
% 2.04/0.66  fof(f286,plain,(
% 2.04/0.66    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.04/0.66    inference(superposition,[],[f282,f144])).
% 2.04/0.66  fof(f274,plain,(
% 2.04/0.66    spl4_21 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.04/0.66    inference(avatar_split_clause,[],[f269,f178,f172,f162,f157,f147,f271])).
% 2.04/0.66  fof(f269,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f268,f174])).
% 2.04/0.66  fof(f268,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f267,f164])).
% 2.04/0.66  fof(f267,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f266,f159])).
% 2.04/0.66  fof(f266,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.04/0.66    inference(subsumption_resolution,[],[f263,f149])).
% 2.04/0.66  fof(f263,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.04/0.66    inference(superposition,[],[f180,f95])).
% 2.04/0.66  fof(f244,plain,(
% 2.04/0.66    spl4_19 | ~spl4_6 | ~spl4_10),
% 2.04/0.66    inference(avatar_split_clause,[],[f243,f162,f142,f239])).
% 2.04/0.66  fof(f243,plain,(
% 2.04/0.66    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 2.04/0.66    inference(subsumption_resolution,[],[f236,f164])).
% 2.04/0.66  fof(f236,plain,(
% 2.04/0.66    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 2.04/0.66    inference(superposition,[],[f144,f96])).
% 2.04/0.66  fof(f197,plain,(
% 2.04/0.66    spl4_15 | ~spl4_10),
% 2.04/0.66    inference(avatar_split_clause,[],[f192,f162,f194])).
% 2.04/0.66  fof(f192,plain,(
% 2.04/0.66    v1_relat_1(sK2) | ~spl4_10),
% 2.04/0.66    inference(subsumption_resolution,[],[f184,f100])).
% 2.04/0.66  fof(f100,plain,(
% 2.04/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f3])).
% 2.04/0.66  fof(f3,axiom,(
% 2.04/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.04/0.66  fof(f184,plain,(
% 2.04/0.66    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.04/0.66    inference(resolution,[],[f99,f164])).
% 2.04/0.66  fof(f99,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f50])).
% 2.04/0.66  fof(f50,plain,(
% 2.04/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.04/0.66    inference(ennf_transformation,[],[f2])).
% 2.04/0.66  fof(f2,axiom,(
% 2.04/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.04/0.66  fof(f191,plain,(
% 2.04/0.66    spl4_14 | ~spl4_7),
% 2.04/0.66    inference(avatar_split_clause,[],[f186,f147,f188])).
% 2.04/0.66  fof(f186,plain,(
% 2.04/0.66    v1_relat_1(sK3) | ~spl4_7),
% 2.04/0.66    inference(subsumption_resolution,[],[f183,f100])).
% 2.04/0.66  fof(f183,plain,(
% 2.04/0.66    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.04/0.66    inference(resolution,[],[f99,f149])).
% 2.04/0.66  fof(f181,plain,(
% 2.04/0.66    spl4_13 | ~spl4_5),
% 2.04/0.66    inference(avatar_split_clause,[],[f176,f137,f178])).
% 2.04/0.66  fof(f137,plain,(
% 2.04/0.66    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.04/0.66  fof(f176,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.04/0.66    inference(backward_demodulation,[],[f139,f92])).
% 2.04/0.66  fof(f139,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.04/0.66    inference(avatar_component_clause,[],[f137])).
% 2.04/0.66  fof(f175,plain,(
% 2.04/0.66    spl4_12),
% 2.04/0.66    inference(avatar_split_clause,[],[f63,f172])).
% 2.04/0.66  fof(f63,plain,(
% 2.04/0.66    v1_funct_1(sK2)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f59,plain,(
% 2.04/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f58,f57])).
% 2.04/0.66  fof(f57,plain,(
% 2.04/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f58,plain,(
% 2.04/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f28,plain,(
% 2.04/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.04/0.66    inference(flattening,[],[f27])).
% 2.04/0.66  fof(f27,plain,(
% 2.04/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.04/0.66    inference(ennf_transformation,[],[f25])).
% 2.04/0.66  fof(f25,negated_conjecture,(
% 2.04/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.04/0.66    inference(negated_conjecture,[],[f24])).
% 2.04/0.66  fof(f24,conjecture,(
% 2.04/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.04/0.66  fof(f170,plain,(
% 2.04/0.66    spl4_11),
% 2.04/0.66    inference(avatar_split_clause,[],[f64,f167])).
% 2.04/0.66  fof(f64,plain,(
% 2.04/0.66    v1_funct_2(sK2,sK0,sK1)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f165,plain,(
% 2.04/0.66    spl4_10),
% 2.04/0.66    inference(avatar_split_clause,[],[f65,f162])).
% 2.04/0.66  fof(f65,plain,(
% 2.04/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f160,plain,(
% 2.04/0.66    spl4_9),
% 2.04/0.66    inference(avatar_split_clause,[],[f66,f157])).
% 2.04/0.66  fof(f66,plain,(
% 2.04/0.66    v1_funct_1(sK3)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f155,plain,(
% 2.04/0.66    spl4_8),
% 2.04/0.66    inference(avatar_split_clause,[],[f67,f152])).
% 2.04/0.66  fof(f67,plain,(
% 2.04/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f150,plain,(
% 2.04/0.66    spl4_7),
% 2.04/0.66    inference(avatar_split_clause,[],[f68,f147])).
% 2.04/0.66  fof(f68,plain,(
% 2.04/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f145,plain,(
% 2.04/0.66    spl4_6),
% 2.04/0.66    inference(avatar_split_clause,[],[f69,f142])).
% 2.04/0.66  fof(f69,plain,(
% 2.04/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f140,plain,(
% 2.04/0.66    spl4_5),
% 2.04/0.66    inference(avatar_split_clause,[],[f70,f137])).
% 2.04/0.66  fof(f70,plain,(
% 2.04/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f135,plain,(
% 2.04/0.66    spl4_4),
% 2.04/0.66    inference(avatar_split_clause,[],[f71,f132])).
% 2.04/0.66  fof(f71,plain,(
% 2.04/0.66    v2_funct_1(sK2)),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f130,plain,(
% 2.04/0.66    ~spl4_3),
% 2.04/0.66    inference(avatar_split_clause,[],[f72,f127])).
% 2.04/0.66  fof(f72,plain,(
% 2.04/0.66    k1_xboole_0 != sK0),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f125,plain,(
% 2.04/0.66    ~spl4_2),
% 2.04/0.66    inference(avatar_split_clause,[],[f73,f122])).
% 2.04/0.66  fof(f73,plain,(
% 2.04/0.66    k1_xboole_0 != sK1),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  fof(f120,plain,(
% 2.04/0.66    ~spl4_1),
% 2.04/0.66    inference(avatar_split_clause,[],[f74,f117])).
% 2.04/0.66  fof(f117,plain,(
% 2.04/0.66    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.04/0.66  fof(f74,plain,(
% 2.04/0.66    k2_funct_1(sK2) != sK3),
% 2.04/0.66    inference(cnf_transformation,[],[f59])).
% 2.04/0.66  % SZS output end Proof for theBenchmark
% 2.04/0.66  % (12244)------------------------------
% 2.04/0.66  % (12244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.66  % (12244)Termination reason: Refutation
% 2.04/0.66  
% 2.04/0.66  % (12244)Memory used [KB]: 7675
% 2.04/0.66  % (12244)Time elapsed: 0.239 s
% 2.04/0.66  % (12244)------------------------------
% 2.04/0.66  % (12244)------------------------------
% 2.04/0.66  % (12222)Success in time 0.299 s
%------------------------------------------------------------------------------
