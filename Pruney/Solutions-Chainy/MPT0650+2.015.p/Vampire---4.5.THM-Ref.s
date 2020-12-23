%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:46 EST 2020

% Result     : Theorem 5.65s
% Output     : Refutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 452 expanded)
%              Number of leaves         :   53 ( 182 expanded)
%              Depth                    :   14
%              Number of atoms          :  911 (1565 expanded)
%              Number of equality atoms :  119 ( 238 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31681)Time limit reached!
% (31681)------------------------------
% (31681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31681)Termination reason: Time limit
% (31681)Termination phase: Saturation

% (31681)Memory used [KB]: 7419
% (31681)Time elapsed: 0.600 s
% (31681)------------------------------
% (31681)------------------------------
fof(f12787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f169,f572,f619,f862,f2147,f4149,f4165,f4173,f7660,f8685,f8707,f8709,f8755,f8771,f10497,f10501,f10502,f10512,f12723,f12786])).

fof(f12786,plain,
    ( ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | ~ spl18_79
    | ~ spl18_118
    | spl18_1314
    | ~ spl18_1448 ),
    inference(avatar_contradiction_clause,[],[f12785])).

fof(f12785,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | ~ spl18_79
    | ~ spl18_118
    | spl18_1314
    | ~ spl18_1448 ),
    inference(subsumption_resolution,[],[f12784,f10511])).

fof(f10511,plain,
    ( ~ r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)))
    | spl18_1314 ),
    inference(avatar_component_clause,[],[f10509])).

fof(f10509,plain,
    ( spl18_1314
  <=> r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1314])])).

fof(f12784,plain,
    ( r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)))
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | ~ spl18_79
    | ~ spl18_118
    | ~ spl18_1448 ),
    inference(forward_demodulation,[],[f12776,f11011])).

fof(f11011,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK10),X0)
    | ~ spl18_7 ),
    inference(backward_demodulation,[],[f7558,f11009])).

fof(f11009,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f2388,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( sK13(X0,X1) != k1_funct_1(X0,sK13(X0,X1))
          & r2_hidden(sK13(X0,X1),X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != X2
          & r2_hidden(X2,X1) )
     => ( sK13(X0,X1) != k1_funct_1(X0,sK13(X0,X1))
        & r2_hidden(sK13(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( k1_funct_1(X0,X2) != X2
            & r2_hidden(X2,X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( ! [X2] :
            ( k1_funct_1(X1,X2) = X2
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2388,plain,(
    ! [X0] : sP2(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f2387,f84])).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f2387,plain,(
    ! [X0] :
      ( sP2(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f2386,f85])).

fof(f85,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2386,plain,(
    ! [X0] :
      ( sP2(k6_relat_1(X0),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f127,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f25,f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> sP2(X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f127,plain,(
    ! [X0] :
      ( ~ sP3(X0,k6_relat_1(X0))
      | sP2(k6_relat_1(X0),X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k6_relat_1(X0) != X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f7558,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(k6_relat_1(X0)))
    | ~ spl18_7 ),
    inference(unit_resulting_resolution,[],[f168,f84,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f168,plain,
    ( v1_relat_1(k4_relat_1(sK10))
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl18_7
  <=> v1_relat_1(k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f12776,plain,
    ( r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(k1_relat_1(sK10)))))
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118
    | ~ spl18_1448 ),
    inference(unit_resulting_resolution,[],[f4460,f12722,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2))))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2))))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2)))) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ sP7(X1,X0,X2) )
        & ( sP7(X1,X0,X2)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ sP8(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> sP7(X1,X0,X2) )
      | ~ sP8(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f12722,plain,
    ( sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10))
    | ~ spl18_1448 ),
    inference(avatar_component_clause,[],[f12720])).

fof(f12720,plain,
    ( spl18_1448
  <=> sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1448])])).

fof(f4460,plain,
    ( ! [X21,X22] : sP8(k4_relat_1(sK10),X21,X22)
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4459,f161])).

fof(f161,plain,
    ( v1_relat_1(sK10)
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl18_6
  <=> v1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f4459,plain,
    ( ! [X21,X22] :
        ( sP8(k4_relat_1(sK10),X21,X22)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4458,f156])).

fof(f156,plain,
    ( v1_funct_1(sK10)
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl18_5
  <=> v1_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f4458,plain,
    ( ! [X21,X22] :
        ( sP8(k4_relat_1(sK10),X21,X22)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_4
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4035,f151])).

fof(f151,plain,
    ( v2_funct_1(sK10)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl18_4
  <=> v2_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f4035,plain,
    ( ! [X21,X22] :
        ( sP8(k4_relat_1(sK10),X21,X22)
        | ~ v2_funct_1(sK10)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(superposition,[],[f1914,f97])).

fof(f97,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1914,plain,
    ( ! [X0,X1] : sP8(k2_funct_1(sK10),X0,X1)
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(unit_resulting_resolution,[],[f618,f861,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( sP8(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP8(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f33,f46,f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( sP7(X1,X0,X2)
    <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f861,plain,
    ( v1_funct_1(k2_funct_1(sK10))
    | ~ spl18_118 ),
    inference(avatar_component_clause,[],[f859])).

fof(f859,plain,
    ( spl18_118
  <=> v1_funct_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_118])])).

fof(f618,plain,
    ( v1_relat_1(k2_funct_1(sK10))
    | ~ spl18_79 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl18_79
  <=> v1_relat_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_79])])).

fof(f12723,plain,
    ( spl18_1448
    | ~ spl18_1141
    | ~ spl18_1313 ),
    inference(avatar_split_clause,[],[f12674,f10494,f8699,f12720])).

fof(f8699,plain,
    ( spl18_1141
  <=> r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1141])])).

fof(f10494,plain,
    ( spl18_1313
  <=> sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1313])])).

fof(f12674,plain,
    ( sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10))
    | ~ spl18_1141
    | ~ spl18_1313 ),
    inference(unit_resulting_resolution,[],[f10495,f8701,f8876])).

fof(f8876,plain,(
    ! [X6,X4,X7,X5] :
      ( sP7(X7,X5,X4)
      | ~ r2_hidden(X6,X7)
      | ~ sP5(X6,X5,X4) ) ),
    inference(subsumption_resolution,[],[f8875,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f8875,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X6,X7)
      | sP7(X7,X5,X4)
      | ~ r2_hidden(X5,k1_relat_1(X4))
      | ~ sP5(X6,X5,X4) ) ),
    inference(superposition,[],[f124,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X1),X0)
      | sP7(X0,X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ~ r2_hidden(k1_funct_1(X2,X1),X0)
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X1),X0)
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f8701,plain,
    ( r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10))
    | ~ spl18_1141 ),
    inference(avatar_component_clause,[],[f8699])).

fof(f10495,plain,
    ( sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10))
    | ~ spl18_1313 ),
    inference(avatar_component_clause,[],[f10494])).

fof(f10512,plain,
    ( ~ spl18_578
    | ~ spl18_1314
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | spl18_579
    | ~ spl18_580
    | ~ spl18_952 ),
    inference(avatar_split_clause,[],[f10507,f7657,f4170,f4162,f166,f159,f154,f10509,f4154])).

fof(f4154,plain,
    ( spl18_578
  <=> sK9 = k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_578])])).

fof(f4162,plain,
    ( spl18_579
  <=> sK9 = k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_579])])).

fof(f4170,plain,
    ( spl18_580
  <=> v1_funct_1(k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_580])])).

fof(f7657,plain,
    ( spl18_952
  <=> k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_952])])).

fof(f10507,plain,
    ( ~ r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)))
    | sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | spl18_579
    | ~ spl18_580
    | ~ spl18_952 ),
    inference(forward_demodulation,[],[f10506,f7659])).

fof(f7659,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))
    | ~ spl18_952 ),
    inference(avatar_component_clause,[],[f7657])).

fof(f10506,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)))
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_7
    | spl18_579
    | ~ spl18_580 ),
    inference(subsumption_resolution,[],[f10505,f161])).

fof(f10505,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)))
    | ~ v1_relat_1(sK10)
    | ~ spl18_5
    | ~ spl18_7
    | spl18_579
    | ~ spl18_580 ),
    inference(subsumption_resolution,[],[f10504,f156])).

fof(f10504,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl18_7
    | spl18_579
    | ~ spl18_580 ),
    inference(subsumption_resolution,[],[f10503,f168])).

fof(f10503,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)))
    | ~ v1_relat_1(k4_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl18_579
    | ~ spl18_580 ),
    inference(subsumption_resolution,[],[f10290,f4172])).

fof(f4172,plain,
    ( v1_funct_1(k4_relat_1(sK10))
    | ~ spl18_580 ),
    inference(avatar_component_clause,[],[f4170])).

fof(f10290,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))
    | ~ r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)))
    | ~ v1_funct_1(k4_relat_1(sK10))
    | ~ v1_relat_1(k4_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl18_579 ),
    inference(superposition,[],[f4164,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f4164,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)
    | spl18_579 ),
    inference(avatar_component_clause,[],[f4162])).

fof(f10502,plain,
    ( k2_funct_1(sK10) != k4_relat_1(sK10)
    | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))
    | sK9 = k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f10501,plain,
    ( ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118
    | ~ spl18_1142
    | spl18_1313 ),
    inference(avatar_contradiction_clause,[],[f10500])).

fof(f10500,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118
    | ~ spl18_1142
    | spl18_1313 ),
    inference(subsumption_resolution,[],[f10498,f8706])).

fof(f8706,plain,
    ( r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10))
    | ~ spl18_1142 ),
    inference(avatar_component_clause,[],[f8704])).

fof(f8704,plain,
    ( spl18_1142
  <=> r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1142])])).

fof(f10498,plain,
    ( ~ r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10))
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118
    | spl18_1313 ),
    inference(unit_resulting_resolution,[],[f4427,f10496,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP5(X1,X0,X2) )
        & ( sP5(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP6(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP5(X1,X0,X2) )
      | ~ sP6(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f10496,plain,
    ( ~ sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10))
    | spl18_1313 ),
    inference(avatar_component_clause,[],[f10494])).

fof(f4427,plain,
    ( ! [X15,X16] : sP6(k4_relat_1(sK10),X15,X16)
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4426,f161])).

fof(f4426,plain,
    ( ! [X15,X16] :
        ( sP6(k4_relat_1(sK10),X15,X16)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4425,f156])).

fof(f4425,plain,
    ( ! [X15,X16] :
        ( sP6(k4_relat_1(sK10),X15,X16)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_4
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4026,f151])).

fof(f4026,plain,
    ( ! [X15,X16] :
        ( sP6(k4_relat_1(sK10),X15,X16)
        | ~ v2_funct_1(sK10)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(superposition,[],[f1529,f97])).

fof(f1529,plain,
    ( ! [X0,X1] : sP6(k2_funct_1(sK10),X0,X1)
    | ~ spl18_79
    | ~ spl18_118 ),
    inference(unit_resulting_resolution,[],[f618,f861,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( sP6(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f31,f43,f42])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f10497,plain,
    ( ~ spl18_1313
    | spl18_1
    | ~ spl18_577
    | ~ spl18_1148 ),
    inference(avatar_split_clause,[],[f10490,f8768,f4146,f135,f10494])).

fof(f135,plain,
    ( spl18_1
  <=> sK9 = k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f4146,plain,
    ( spl18_577
  <=> k2_funct_1(sK10) = k4_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_577])])).

fof(f8768,plain,
    ( spl18_1148
  <=> sK9 = k1_funct_1(sK10,sK16(sK10,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1148])])).

fof(f10490,plain,
    ( ~ sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10))
    | spl18_1
    | ~ spl18_577
    | ~ spl18_1148 ),
    inference(unit_resulting_resolution,[],[f8770,f5158])).

fof(f5158,plain,
    ( ! [X1] :
        ( ~ sP5(X1,sK9,k4_relat_1(sK10))
        | sK9 != k1_funct_1(sK10,X1) )
    | spl18_1
    | ~ spl18_577 ),
    inference(backward_demodulation,[],[f2393,f4148])).

fof(f4148,plain,
    ( k2_funct_1(sK10) = k4_relat_1(sK10)
    | ~ spl18_577 ),
    inference(avatar_component_clause,[],[f4146])).

fof(f2393,plain,
    ( ! [X1] :
        ( sK9 != k1_funct_1(sK10,X1)
        | ~ sP5(X1,sK9,k2_funct_1(sK10)) )
    | spl18_1 ),
    inference(superposition,[],[f137,f117])).

fof(f137,plain,
    ( sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f8770,plain,
    ( sK9 = k1_funct_1(sK10,sK16(sK10,sK9))
    | ~ spl18_1148 ),
    inference(avatar_component_clause,[],[f8768])).

fof(f8771,plain,
    ( spl18_1148
    | ~ spl18_1144 ),
    inference(avatar_split_clause,[],[f8764,f8740,f8768])).

fof(f8740,plain,
    ( spl18_1144
  <=> sP5(sK9,sK16(sK10,sK9),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1144])])).

fof(f8764,plain,
    ( sK9 = k1_funct_1(sK10,sK16(sK10,sK9))
    | ~ spl18_1144 ),
    inference(unit_resulting_resolution,[],[f8742,f117])).

fof(f8742,plain,
    ( sP5(sK9,sK16(sK10,sK9),sK10)
    | ~ spl18_1144 ),
    inference(avatar_component_clause,[],[f8740])).

fof(f8755,plain,
    ( spl18_1144
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_1139 ),
    inference(avatar_split_clause,[],[f8754,f8682,f159,f154,f8740])).

fof(f8682,plain,
    ( spl18_1139
  <=> r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1139])])).

fof(f8754,plain,
    ( sP5(sK9,sK16(sK10,sK9),sK10)
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_1139 ),
    inference(subsumption_resolution,[],[f8738,f1527])).

fof(f1527,plain,
    ( ! [X0,X1] : sP6(sK10,X0,X1)
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(unit_resulting_resolution,[],[f161,f156,f119])).

fof(f8738,plain,
    ( sP5(sK9,sK16(sK10,sK9),sK10)
    | ~ sP6(sK10,sK16(sK10,sK9),sK9)
    | ~ spl18_1139 ),
    inference(resolution,[],[f114,f8684])).

fof(f8684,plain,
    ( r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10)
    | ~ spl18_1139 ),
    inference(avatar_component_clause,[],[f8682])).

fof(f8709,plain,
    ( spl18_1141
    | ~ spl18_6
    | ~ spl18_1139 ),
    inference(avatar_split_clause,[],[f8708,f8682,f159,f8699])).

fof(f8708,plain,
    ( r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10))
    | ~ spl18_6
    | ~ spl18_1139 ),
    inference(subsumption_resolution,[],[f8691,f161])).

fof(f8691,plain,
    ( r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | ~ spl18_1139 ),
    inference(resolution,[],[f8684,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f8707,plain,
    ( spl18_1142
    | ~ spl18_323
    | ~ spl18_1139 ),
    inference(avatar_split_clause,[],[f8686,f8682,f2143,f8704])).

fof(f2143,plain,
    ( spl18_323
  <=> sP0(sK10,k4_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_323])])).

fof(f8686,plain,
    ( r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10))
    | ~ spl18_323
    | ~ spl18_1139 ),
    inference(unit_resulting_resolution,[],[f2145,f8684,f91])).

fof(f91,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
            | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
          & ( r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2145,plain,
    ( sP0(sK10,k4_relat_1(sK10))
    | ~ spl18_323 ),
    inference(avatar_component_clause,[],[f2143])).

fof(f8685,plain,
    ( spl18_1139
    | ~ spl18_3 ),
    inference(avatar_split_clause,[],[f8677,f144,f8682])).

fof(f144,plain,
    ( spl18_3
  <=> r2_hidden(sK9,k2_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f8677,plain,
    ( r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10)
    | ~ spl18_3 ),
    inference(unit_resulting_resolution,[],[f130,f146,f106])).

fof(f106,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK16(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK14(X0,X1)),X0)
            | ~ r2_hidden(sK14(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK15(X0,X1),sK14(X0,X1)),X0)
            | r2_hidden(sK14(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK16(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f63,f66,f65,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK14(X0,X1)),X0)
          | ~ r2_hidden(sK14(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK14(X0,X1)),X0)
          | r2_hidden(sK14(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK14(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK15(X0,X1),sK14(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK16(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f146,plain,
    ( r2_hidden(sK9,k2_relat_1(sK10))
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f130,plain,(
    ! [X0] : sP4(X0,k2_relat_1(X0)) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ~ sP4(X0,X1) )
      & ( sP4(X0,X1)
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> sP4(X0,X1) ) ),
    inference(definition_folding,[],[f1,f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f7660,plain,
    ( spl18_952
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(avatar_split_clause,[],[f7573,f166,f159,f7657])).

fof(f7573,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(unit_resulting_resolution,[],[f168,f161,f87])).

fof(f4173,plain,
    ( spl18_580
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_118 ),
    inference(avatar_split_clause,[],[f4168,f859,f159,f154,f149,f4170])).

fof(f4168,plain,
    ( v1_funct_1(k4_relat_1(sK10))
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4167,f161])).

fof(f4167,plain,
    ( v1_funct_1(k4_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f4166,f156])).

fof(f4166,plain,
    ( v1_funct_1(k4_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl18_4
    | ~ spl18_118 ),
    inference(subsumption_resolution,[],[f3975,f151])).

fof(f3975,plain,
    ( v1_funct_1(k4_relat_1(sK10))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl18_118 ),
    inference(superposition,[],[f861,f97])).

fof(f4165,plain,
    ( ~ spl18_579
    | spl18_2
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(avatar_split_clause,[],[f4160,f159,f154,f149,f139,f4162])).

fof(f139,plain,
    ( spl18_2
  <=> sK9 = k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f4160,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)
    | spl18_2
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f4159,f161])).

fof(f4159,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)
    | ~ v1_relat_1(sK10)
    | spl18_2
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f4158,f156])).

fof(f4158,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3948,f151])).

fof(f3948,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl18_2 ),
    inference(superposition,[],[f141,f97])).

fof(f141,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9)
    | spl18_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f4149,plain,
    ( spl18_577
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(avatar_split_clause,[],[f3946,f159,f154,f149,f4146])).

fof(f3946,plain,
    ( k2_funct_1(sK10) = k4_relat_1(sK10)
    | ~ spl18_4
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(unit_resulting_resolution,[],[f161,f156,f151,f97])).

fof(f2147,plain,
    ( spl18_323
    | ~ spl18_70 ),
    inference(avatar_split_clause,[],[f2128,f569,f2143])).

fof(f569,plain,
    ( spl18_70
  <=> sP1(k4_relat_1(sK10),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).

fof(f2128,plain,
    ( sP0(sK10,k4_relat_1(sK10))
    | ~ spl18_70 ),
    inference(resolution,[],[f126,f571])).

fof(f571,plain,
    ( sP1(k4_relat_1(sK10),sK10)
    | ~ spl18_70 ),
    inference(avatar_component_clause,[],[f569])).

fof(f126,plain,(
    ! [X1] :
      ( ~ sP1(k4_relat_1(X1),X1)
      | sP0(X1,k4_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k4_relat_1(X1) != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k4_relat_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k4_relat_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ( ( k4_relat_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k4_relat_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( k4_relat_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f862,plain,
    ( spl18_118
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(avatar_split_clause,[],[f856,f159,f154,f859])).

fof(f856,plain,
    ( v1_funct_1(k2_funct_1(sK10))
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(unit_resulting_resolution,[],[f161,f156,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f619,plain,
    ( spl18_79
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(avatar_split_clause,[],[f613,f159,f154,f616])).

fof(f613,plain,
    ( v1_relat_1(k2_funct_1(sK10))
    | ~ spl18_5
    | ~ spl18_6 ),
    inference(unit_resulting_resolution,[],[f161,f156,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f572,plain,
    ( spl18_70
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(avatar_split_clause,[],[f230,f166,f159,f569])).

fof(f230,plain,
    ( sP1(k4_relat_1(sK10),sK10)
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(unit_resulting_resolution,[],[f161,f168,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f35,f34])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f169,plain,
    ( spl18_7
    | ~ spl18_6 ),
    inference(avatar_split_clause,[],[f163,f159,f166])).

fof(f163,plain,
    ( v1_relat_1(k4_relat_1(sK10))
    | ~ spl18_6 ),
    inference(unit_resulting_resolution,[],[f161,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f162,plain,(
    spl18_6 ),
    inference(avatar_split_clause,[],[f79,f159])).

fof(f79,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9)
      | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) )
    & r2_hidden(sK9,k2_relat_1(sK10))
    & v2_funct_1(sK10)
    & v1_funct_1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f16,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9)
        | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) )
      & r2_hidden(sK9,k2_relat_1(sK10))
      & v2_funct_1(sK10)
      & v1_funct_1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f157,plain,(
    spl18_5 ),
    inference(avatar_split_clause,[],[f80,f154])).

fof(f80,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f49])).

fof(f152,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f81,f149])).

fof(f81,plain,(
    v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f49])).

fof(f147,plain,(
    spl18_3 ),
    inference(avatar_split_clause,[],[f82,f144])).

fof(f82,plain,(
    r2_hidden(sK9,k2_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f49])).

fof(f142,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f83,f139,f135])).

fof(f83,plain,
    ( sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9)
    | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (31673)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (31673)Refutation not found, incomplete strategy% (31673)------------------------------
% 0.21/0.47  % (31673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (31673)Memory used [KB]: 10618
% 0.21/0.47  % (31673)Time elapsed: 0.056 s
% 0.21/0.47  % (31673)------------------------------
% 0.21/0.47  % (31673)------------------------------
% 0.21/0.48  % (31685)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (31687)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (31678)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (31679)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (31680)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (31674)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (31689)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (31682)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.54  % (31688)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.55/0.56  % (31691)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.55/0.56  % (31692)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.55/0.57  % (31684)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.55/0.57  % (31675)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.67/0.57  % (31690)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.67/0.58  % (31681)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.67/0.59  % (31672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.67/0.61  % (31677)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.67/0.62  % (31694)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.67/0.63  % (31694)Refutation not found, incomplete strategy% (31694)------------------------------
% 1.67/0.63  % (31694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.63  % (31694)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.63  
% 1.67/0.63  % (31694)Memory used [KB]: 10618
% 1.67/0.63  % (31694)Time elapsed: 0.193 s
% 1.67/0.63  % (31694)------------------------------
% 1.67/0.63  % (31694)------------------------------
% 1.67/0.64  % (31686)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.67/0.64  % (31693)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 4.07/0.94  % (31686)Time limit reached!
% 4.07/0.94  % (31686)------------------------------
% 4.07/0.94  % (31686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (31686)Termination reason: Time limit
% 4.07/0.94  % (31686)Termination phase: Saturation
% 4.07/0.94  
% 4.07/0.94  % (31686)Memory used [KB]: 9338
% 4.07/0.94  % (31686)Time elapsed: 0.500 s
% 4.07/0.94  % (31686)------------------------------
% 4.07/0.94  % (31686)------------------------------
% 4.62/0.95  % (31678)Time limit reached!
% 4.62/0.95  % (31678)------------------------------
% 4.62/0.95  % (31678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.95  % (31678)Termination reason: Time limit
% 4.62/0.95  
% 4.62/0.95  % (31678)Memory used [KB]: 8699
% 4.62/0.95  % (31678)Time elapsed: 0.516 s
% 4.62/0.95  % (31678)------------------------------
% 4.62/0.95  % (31678)------------------------------
% 4.62/0.96  % (31684)Time limit reached!
% 4.62/0.96  % (31684)------------------------------
% 4.62/0.96  % (31684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.96  % (31684)Termination reason: Time limit
% 4.62/0.96  
% 4.62/0.96  % (31684)Memory used [KB]: 9083
% 4.62/0.96  % (31684)Time elapsed: 0.524 s
% 4.62/0.96  % (31684)------------------------------
% 4.62/0.96  % (31684)------------------------------
% 4.90/0.99  % (31672)Time limit reached!
% 4.90/0.99  % (31672)------------------------------
% 4.90/0.99  % (31672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.90/0.99  % (31672)Termination reason: Time limit
% 4.90/0.99  % (31672)Termination phase: Saturation
% 4.90/0.99  
% 4.90/0.99  % (31672)Memory used [KB]: 8699
% 4.90/0.99  % (31672)Time elapsed: 0.500 s
% 4.90/0.99  % (31672)------------------------------
% 4.90/0.99  % (31672)------------------------------
% 5.65/1.08  % (31690)Refutation found. Thanks to Tanya!
% 5.65/1.08  % SZS status Theorem for theBenchmark
% 5.65/1.08  % SZS output start Proof for theBenchmark
% 5.65/1.08  % (31681)Time limit reached!
% 5.65/1.08  % (31681)------------------------------
% 5.65/1.08  % (31681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.08  % (31681)Termination reason: Time limit
% 5.65/1.08  % (31681)Termination phase: Saturation
% 5.65/1.08  
% 5.65/1.08  % (31681)Memory used [KB]: 7419
% 5.65/1.08  % (31681)Time elapsed: 0.600 s
% 5.65/1.08  % (31681)------------------------------
% 5.65/1.08  % (31681)------------------------------
% 5.65/1.08  fof(f12787,plain,(
% 5.65/1.08    $false),
% 5.65/1.08    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f169,f572,f619,f862,f2147,f4149,f4165,f4173,f7660,f8685,f8707,f8709,f8755,f8771,f10497,f10501,f10502,f10512,f12723,f12786])).
% 5.65/1.08  fof(f12786,plain,(
% 5.65/1.08    ~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_7 | ~spl18_79 | ~spl18_118 | spl18_1314 | ~spl18_1448),
% 5.65/1.08    inference(avatar_contradiction_clause,[],[f12785])).
% 5.65/1.08  fof(f12785,plain,(
% 5.65/1.08    $false | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_7 | ~spl18_79 | ~spl18_118 | spl18_1314 | ~spl18_1448)),
% 5.65/1.08    inference(subsumption_resolution,[],[f12784,f10511])).
% 5.65/1.08  fof(f10511,plain,(
% 5.65/1.08    ~r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))) | spl18_1314),
% 5.65/1.08    inference(avatar_component_clause,[],[f10509])).
% 5.65/1.08  fof(f10509,plain,(
% 5.65/1.08    spl18_1314 <=> r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)))),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_1314])])).
% 5.65/1.08  fof(f12784,plain,(
% 5.65/1.08    r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_7 | ~spl18_79 | ~spl18_118 | ~spl18_1448)),
% 5.65/1.08    inference(forward_demodulation,[],[f12776,f11011])).
% 5.65/1.08  fof(f11011,plain,(
% 5.65/1.08    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK10),X0)) ) | ~spl18_7),
% 5.65/1.08    inference(backward_demodulation,[],[f7558,f11009])).
% 5.65/1.08  fof(f11009,plain,(
% 5.65/1.08    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 5.65/1.08    inference(unit_resulting_resolution,[],[f2388,f100])).
% 5.65/1.08  fof(f100,plain,(
% 5.65/1.08    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | ~sP2(X0,X1)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f61])).
% 5.65/1.08  fof(f61,plain,(
% 5.65/1.08    ! [X0,X1] : ((sP2(X0,X1) | (sK13(X0,X1) != k1_funct_1(X0,sK13(X0,X1)) & r2_hidden(sK13(X0,X1),X1)) | k1_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X0,X3) = X3 | ~r2_hidden(X3,X1)) & k1_relat_1(X0) = X1) | ~sP2(X0,X1)))),
% 5.65/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f59,f60])).
% 5.65/1.08  fof(f60,plain,(
% 5.65/1.08    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != X2 & r2_hidden(X2,X1)) => (sK13(X0,X1) != k1_funct_1(X0,sK13(X0,X1)) & r2_hidden(sK13(X0,X1),X1)))),
% 5.65/1.08    introduced(choice_axiom,[])).
% 5.65/1.08  fof(f59,plain,(
% 5.65/1.08    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != X2 & r2_hidden(X2,X1)) | k1_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X0,X3) = X3 | ~r2_hidden(X3,X1)) & k1_relat_1(X0) = X1) | ~sP2(X0,X1)))),
% 5.65/1.08    inference(rectify,[],[f58])).
% 5.65/1.08  fof(f58,plain,(
% 5.65/1.08    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | ~sP2(X1,X0)))),
% 5.65/1.08    inference(flattening,[],[f57])).
% 5.65/1.08  fof(f57,plain,(
% 5.65/1.08    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | ~sP2(X1,X0)))),
% 5.65/1.08    inference(nnf_transformation,[],[f37])).
% 5.65/1.08  fof(f37,plain,(
% 5.65/1.08    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0))),
% 5.65/1.08    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 5.65/1.08  fof(f2388,plain,(
% 5.65/1.08    ( ! [X0] : (sP2(k6_relat_1(X0),X0)) )),
% 5.65/1.08    inference(subsumption_resolution,[],[f2387,f84])).
% 5.65/1.08  fof(f84,plain,(
% 5.65/1.08    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 5.65/1.08    inference(cnf_transformation,[],[f8])).
% 5.65/1.08  fof(f8,axiom,(
% 5.65/1.08    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 5.65/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 5.65/1.08  fof(f2387,plain,(
% 5.65/1.08    ( ! [X0] : (sP2(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.65/1.08    inference(subsumption_resolution,[],[f2386,f85])).
% 5.65/1.08  fof(f85,plain,(
% 5.65/1.08    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 5.65/1.08    inference(cnf_transformation,[],[f8])).
% 5.65/1.08  fof(f2386,plain,(
% 5.65/1.08    ( ! [X0] : (sP2(k6_relat_1(X0),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.65/1.08    inference(resolution,[],[f127,f104])).
% 5.65/1.08  fof(f104,plain,(
% 5.65/1.08    ( ! [X0,X1] : (sP3(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f39])).
% 5.65/1.08  fof(f39,plain,(
% 5.65/1.08    ! [X0,X1] : (sP3(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.65/1.08    inference(definition_folding,[],[f25,f38,f37])).
% 5.65/1.08  fof(f38,plain,(
% 5.65/1.08    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 5.65/1.08    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 5.65/1.08  fof(f25,plain,(
% 5.65/1.08    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.65/1.08    inference(flattening,[],[f24])).
% 5.65/1.08  fof(f24,plain,(
% 5.65/1.08    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.65/1.08    inference(ennf_transformation,[],[f10])).
% 5.65/1.08  fof(f10,axiom,(
% 5.65/1.08    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 5.65/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 5.65/1.08  fof(f127,plain,(
% 5.65/1.08    ( ! [X0] : (~sP3(X0,k6_relat_1(X0)) | sP2(k6_relat_1(X0),X0)) )),
% 5.65/1.08    inference(equality_resolution,[],[f98])).
% 5.65/1.08  fof(f98,plain,(
% 5.65/1.08    ( ! [X0,X1] : (sP2(X1,X0) | k6_relat_1(X0) != X1 | ~sP3(X0,X1)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f56])).
% 5.65/1.08  fof(f56,plain,(
% 5.65/1.08    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ~sP2(X1,X0)) & (sP2(X1,X0) | k6_relat_1(X0) != X1)) | ~sP3(X0,X1))),
% 5.65/1.08    inference(nnf_transformation,[],[f38])).
% 5.65/1.08  fof(f7558,plain,(
% 5.65/1.08    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(k6_relat_1(X0)))) ) | ~spl18_7),
% 5.65/1.08    inference(unit_resulting_resolution,[],[f168,f84,f87])).
% 5.65/1.08  fof(f87,plain,(
% 5.65/1.08    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f18])).
% 5.65/1.08  fof(f18,plain,(
% 5.65/1.08    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.65/1.08    inference(ennf_transformation,[],[f4])).
% 5.65/1.08  fof(f4,axiom,(
% 5.65/1.08    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 5.65/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 5.65/1.08  fof(f168,plain,(
% 5.65/1.08    v1_relat_1(k4_relat_1(sK10)) | ~spl18_7),
% 5.65/1.08    inference(avatar_component_clause,[],[f166])).
% 5.65/1.08  fof(f166,plain,(
% 5.65/1.08    spl18_7 <=> v1_relat_1(k4_relat_1(sK10))),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).
% 5.65/1.08  fof(f12776,plain,(
% 5.65/1.08    r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),k6_relat_1(k1_relat_1(sK10))))) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118 | ~spl18_1448)),
% 5.65/1.08    inference(unit_resulting_resolution,[],[f4460,f12722,f121])).
% 5.65/1.08  fof(f121,plain,(
% 5.65/1.08    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2)))) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f75])).
% 5.65/1.08  fof(f75,plain,(
% 5.65/1.08    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2)))) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2)))))) | ~sP8(X0,X1,X2))),
% 5.65/1.08    inference(rectify,[],[f74])).
% 5.65/1.08  fof(f74,plain,(
% 5.65/1.08    ! [X2,X0,X1] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~sP8(X2,X0,X1))),
% 5.65/1.08    inference(nnf_transformation,[],[f46])).
% 5.65/1.08  fof(f46,plain,(
% 5.65/1.08    ! [X2,X0,X1] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> sP7(X1,X0,X2)) | ~sP8(X2,X0,X1))),
% 5.65/1.08    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 5.65/1.08  fof(f12722,plain,(
% 5.65/1.08    sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10)) | ~spl18_1448),
% 5.65/1.08    inference(avatar_component_clause,[],[f12720])).
% 5.65/1.08  fof(f12720,plain,(
% 5.65/1.08    spl18_1448 <=> sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10))),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_1448])])).
% 5.65/1.08  fof(f4460,plain,(
% 5.65/1.08    ( ! [X21,X22] : (sP8(k4_relat_1(sK10),X21,X22)) ) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118)),
% 5.65/1.08    inference(subsumption_resolution,[],[f4459,f161])).
% 5.65/1.08  fof(f161,plain,(
% 5.65/1.08    v1_relat_1(sK10) | ~spl18_6),
% 5.65/1.08    inference(avatar_component_clause,[],[f159])).
% 5.65/1.08  fof(f159,plain,(
% 5.65/1.08    spl18_6 <=> v1_relat_1(sK10)),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).
% 5.65/1.08  fof(f4459,plain,(
% 5.65/1.08    ( ! [X21,X22] : (sP8(k4_relat_1(sK10),X21,X22) | ~v1_relat_1(sK10)) ) | (~spl18_4 | ~spl18_5 | ~spl18_79 | ~spl18_118)),
% 5.65/1.08    inference(subsumption_resolution,[],[f4458,f156])).
% 5.65/1.08  fof(f156,plain,(
% 5.65/1.08    v1_funct_1(sK10) | ~spl18_5),
% 5.65/1.08    inference(avatar_component_clause,[],[f154])).
% 5.65/1.08  fof(f154,plain,(
% 5.65/1.08    spl18_5 <=> v1_funct_1(sK10)),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 5.65/1.08  fof(f4458,plain,(
% 5.65/1.08    ( ! [X21,X22] : (sP8(k4_relat_1(sK10),X21,X22) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | (~spl18_4 | ~spl18_79 | ~spl18_118)),
% 5.65/1.08    inference(subsumption_resolution,[],[f4035,f151])).
% 5.65/1.08  fof(f151,plain,(
% 5.65/1.08    v2_funct_1(sK10) | ~spl18_4),
% 5.65/1.08    inference(avatar_component_clause,[],[f149])).
% 5.65/1.08  fof(f149,plain,(
% 5.65/1.08    spl18_4 <=> v2_funct_1(sK10)),
% 5.65/1.08    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 5.65/1.08  fof(f4035,plain,(
% 5.65/1.08    ( ! [X21,X22] : (sP8(k4_relat_1(sK10),X21,X22) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | (~spl18_79 | ~spl18_118)),
% 5.65/1.08    inference(superposition,[],[f1914,f97])).
% 5.65/1.08  fof(f97,plain,(
% 5.65/1.08    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f23])).
% 5.65/1.08  fof(f23,plain,(
% 5.65/1.08    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.65/1.08    inference(flattening,[],[f22])).
% 5.65/1.08  fof(f22,plain,(
% 5.65/1.08    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.65/1.08    inference(ennf_transformation,[],[f6])).
% 5.65/1.08  fof(f6,axiom,(
% 5.65/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 5.65/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 5.65/1.08  fof(f1914,plain,(
% 5.65/1.08    ( ! [X0,X1] : (sP8(k2_funct_1(sK10),X0,X1)) ) | (~spl18_79 | ~spl18_118)),
% 5.65/1.08    inference(unit_resulting_resolution,[],[f618,f861,f125])).
% 5.65/1.08  fof(f125,plain,(
% 5.65/1.08    ( ! [X2,X0,X1] : (sP8(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.65/1.08    inference(cnf_transformation,[],[f47])).
% 5.65/1.09  fof(f47,plain,(
% 5.65/1.09    ! [X0,X1,X2] : (sP8(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(definition_folding,[],[f33,f46,f45])).
% 5.65/1.09  fof(f45,plain,(
% 5.65/1.09    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 5.65/1.09  fof(f33,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(flattening,[],[f32])).
% 5.65/1.09  fof(f32,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.65/1.09    inference(ennf_transformation,[],[f11])).
% 5.65/1.09  fof(f11,axiom,(
% 5.65/1.09    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 5.65/1.09  fof(f861,plain,(
% 5.65/1.09    v1_funct_1(k2_funct_1(sK10)) | ~spl18_118),
% 5.65/1.09    inference(avatar_component_clause,[],[f859])).
% 5.65/1.09  fof(f859,plain,(
% 5.65/1.09    spl18_118 <=> v1_funct_1(k2_funct_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_118])])).
% 5.65/1.09  fof(f618,plain,(
% 5.65/1.09    v1_relat_1(k2_funct_1(sK10)) | ~spl18_79),
% 5.65/1.09    inference(avatar_component_clause,[],[f616])).
% 5.65/1.09  fof(f616,plain,(
% 5.65/1.09    spl18_79 <=> v1_relat_1(k2_funct_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_79])])).
% 5.65/1.09  fof(f12723,plain,(
% 5.65/1.09    spl18_1448 | ~spl18_1141 | ~spl18_1313),
% 5.65/1.09    inference(avatar_split_clause,[],[f12674,f10494,f8699,f12720])).
% 5.65/1.09  fof(f8699,plain,(
% 5.65/1.09    spl18_1141 <=> r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1141])])).
% 5.65/1.09  fof(f10494,plain,(
% 5.65/1.09    spl18_1313 <=> sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1313])])).
% 5.65/1.09  fof(f12674,plain,(
% 5.65/1.09    sP7(k1_relat_1(sK10),sK9,k4_relat_1(sK10)) | (~spl18_1141 | ~spl18_1313)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f10495,f8701,f8876])).
% 5.65/1.09  fof(f8876,plain,(
% 5.65/1.09    ( ! [X6,X4,X7,X5] : (sP7(X7,X5,X4) | ~r2_hidden(X6,X7) | ~sP5(X6,X5,X4)) )),
% 5.65/1.09    inference(subsumption_resolution,[],[f8875,f116])).
% 5.65/1.09  fof(f116,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X2))) )),
% 5.65/1.09    inference(cnf_transformation,[],[f73])).
% 5.65/1.09  fof(f73,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP5(X0,X1,X2)))),
% 5.65/1.09    inference(rectify,[],[f72])).
% 5.65/1.09  fof(f72,plain,(
% 5.65/1.09    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP5(X1,X0,X2)))),
% 5.65/1.09    inference(flattening,[],[f71])).
% 5.65/1.09  fof(f71,plain,(
% 5.65/1.09    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP5(X1,X0,X2)))),
% 5.65/1.09    inference(nnf_transformation,[],[f42])).
% 5.65/1.09  fof(f42,plain,(
% 5.65/1.09    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 5.65/1.09  fof(f8875,plain,(
% 5.65/1.09    ( ! [X6,X4,X7,X5] : (~r2_hidden(X6,X7) | sP7(X7,X5,X4) | ~r2_hidden(X5,k1_relat_1(X4)) | ~sP5(X6,X5,X4)) )),
% 5.65/1.09    inference(superposition,[],[f124,f117])).
% 5.65/1.09  fof(f117,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | ~sP5(X0,X1,X2)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f73])).
% 5.65/1.09  fof(f124,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X1),X0) | sP7(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 5.65/1.09    inference(cnf_transformation,[],[f78])).
% 5.65/1.09  fof(f78,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ~r2_hidden(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) | ~sP7(X0,X1,X2)))),
% 5.65/1.09    inference(rectify,[],[f77])).
% 5.65/1.09  fof(f77,plain,(
% 5.65/1.09    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~sP7(X1,X0,X2)))),
% 5.65/1.09    inference(flattening,[],[f76])).
% 5.65/1.09  fof(f76,plain,(
% 5.65/1.09    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~sP7(X1,X0,X2)))),
% 5.65/1.09    inference(nnf_transformation,[],[f45])).
% 5.65/1.09  fof(f8701,plain,(
% 5.65/1.09    r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10)) | ~spl18_1141),
% 5.65/1.09    inference(avatar_component_clause,[],[f8699])).
% 5.65/1.09  fof(f10495,plain,(
% 5.65/1.09    sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10)) | ~spl18_1313),
% 5.65/1.09    inference(avatar_component_clause,[],[f10494])).
% 5.65/1.09  fof(f10512,plain,(
% 5.65/1.09    ~spl18_578 | ~spl18_1314 | ~spl18_5 | ~spl18_6 | ~spl18_7 | spl18_579 | ~spl18_580 | ~spl18_952),
% 5.65/1.09    inference(avatar_split_clause,[],[f10507,f7657,f4170,f4162,f166,f159,f154,f10509,f4154])).
% 5.65/1.09  fof(f4154,plain,(
% 5.65/1.09    spl18_578 <=> sK9 = k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_578])])).
% 5.65/1.09  fof(f4162,plain,(
% 5.65/1.09    spl18_579 <=> sK9 = k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_579])])).
% 5.65/1.09  fof(f4170,plain,(
% 5.65/1.09    spl18_580 <=> v1_funct_1(k4_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_580])])).
% 5.65/1.09  fof(f7657,plain,(
% 5.65/1.09    spl18_952 <=> k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_952])])).
% 5.65/1.09  fof(f10507,plain,(
% 5.65/1.09    ~r2_hidden(sK9,k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10))) | sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | (~spl18_5 | ~spl18_6 | ~spl18_7 | spl18_579 | ~spl18_580 | ~spl18_952)),
% 5.65/1.09    inference(forward_demodulation,[],[f10506,f7659])).
% 5.65/1.09  fof(f7659,plain,(
% 5.65/1.09    k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)) | ~spl18_952),
% 5.65/1.09    inference(avatar_component_clause,[],[f7657])).
% 5.65/1.09  fof(f10506,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | ~r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10))) | (~spl18_5 | ~spl18_6 | ~spl18_7 | spl18_579 | ~spl18_580)),
% 5.65/1.09    inference(subsumption_resolution,[],[f10505,f161])).
% 5.65/1.09  fof(f10505,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | ~r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10))) | ~v1_relat_1(sK10) | (~spl18_5 | ~spl18_7 | spl18_579 | ~spl18_580)),
% 5.65/1.09    inference(subsumption_resolution,[],[f10504,f156])).
% 5.65/1.09  fof(f10504,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | ~r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10))) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl18_7 | spl18_579 | ~spl18_580)),
% 5.65/1.09    inference(subsumption_resolution,[],[f10503,f168])).
% 5.65/1.09  fof(f10503,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | ~r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10))) | ~v1_relat_1(k4_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (spl18_579 | ~spl18_580)),
% 5.65/1.09    inference(subsumption_resolution,[],[f10290,f4172])).
% 5.65/1.09  fof(f4172,plain,(
% 5.65/1.09    v1_funct_1(k4_relat_1(sK10)) | ~spl18_580),
% 5.65/1.09    inference(avatar_component_clause,[],[f4170])).
% 5.65/1.09  fof(f10290,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9)) | ~r2_hidden(sK9,k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10))) | ~v1_funct_1(k4_relat_1(sK10)) | ~v1_relat_1(k4_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | spl18_579),
% 5.65/1.09    inference(superposition,[],[f4164,f105])).
% 5.65/1.09  fof(f105,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f27])).
% 5.65/1.09  fof(f27,plain,(
% 5.65/1.09    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.65/1.09    inference(flattening,[],[f26])).
% 5.65/1.09  fof(f26,plain,(
% 5.65/1.09    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.65/1.09    inference(ennf_transformation,[],[f9])).
% 5.65/1.09  fof(f9,axiom,(
% 5.65/1.09    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 5.65/1.09  fof(f4164,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) | spl18_579),
% 5.65/1.09    inference(avatar_component_clause,[],[f4162])).
% 5.65/1.09  fof(f10502,plain,(
% 5.65/1.09    k2_funct_1(sK10) != k4_relat_1(sK10) | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) | sK9 = k1_funct_1(sK10,k1_funct_1(k4_relat_1(sK10),sK9))),
% 5.65/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.65/1.09  fof(f10501,plain,(
% 5.65/1.09    ~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118 | ~spl18_1142 | spl18_1313),
% 5.65/1.09    inference(avatar_contradiction_clause,[],[f10500])).
% 5.65/1.09  fof(f10500,plain,(
% 5.65/1.09    $false | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118 | ~spl18_1142 | spl18_1313)),
% 5.65/1.09    inference(subsumption_resolution,[],[f10498,f8706])).
% 5.65/1.09  fof(f8706,plain,(
% 5.65/1.09    r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10)) | ~spl18_1142),
% 5.65/1.09    inference(avatar_component_clause,[],[f8704])).
% 5.65/1.09  fof(f8704,plain,(
% 5.65/1.09    spl18_1142 <=> r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1142])])).
% 5.65/1.09  fof(f10498,plain,(
% 5.65/1.09    ~r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10)) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118 | spl18_1313)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f4427,f10496,f114])).
% 5.65/1.09  fof(f114,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f70])).
% 5.65/1.09  fof(f70,plain,(
% 5.65/1.09    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP6(X0,X1,X2))),
% 5.65/1.09    inference(rectify,[],[f69])).
% 5.65/1.09  fof(f69,plain,(
% 5.65/1.09    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP6(X2,X0,X1))),
% 5.65/1.09    inference(nnf_transformation,[],[f43])).
% 5.65/1.09  fof(f43,plain,(
% 5.65/1.09    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 5.65/1.09  fof(f10496,plain,(
% 5.65/1.09    ~sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10)) | spl18_1313),
% 5.65/1.09    inference(avatar_component_clause,[],[f10494])).
% 5.65/1.09  fof(f4427,plain,(
% 5.65/1.09    ( ! [X15,X16] : (sP6(k4_relat_1(sK10),X15,X16)) ) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_79 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4426,f161])).
% 5.65/1.09  fof(f4426,plain,(
% 5.65/1.09    ( ! [X15,X16] : (sP6(k4_relat_1(sK10),X15,X16) | ~v1_relat_1(sK10)) ) | (~spl18_4 | ~spl18_5 | ~spl18_79 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4425,f156])).
% 5.65/1.09  fof(f4425,plain,(
% 5.65/1.09    ( ! [X15,X16] : (sP6(k4_relat_1(sK10),X15,X16) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | (~spl18_4 | ~spl18_79 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4026,f151])).
% 5.65/1.09  fof(f4026,plain,(
% 5.65/1.09    ( ! [X15,X16] : (sP6(k4_relat_1(sK10),X15,X16) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | (~spl18_79 | ~spl18_118)),
% 5.65/1.09    inference(superposition,[],[f1529,f97])).
% 5.65/1.09  fof(f1529,plain,(
% 5.65/1.09    ( ! [X0,X1] : (sP6(k2_funct_1(sK10),X0,X1)) ) | (~spl18_79 | ~spl18_118)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f618,f861,f119])).
% 5.65/1.09  fof(f119,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f44])).
% 5.65/1.09  fof(f44,plain,(
% 5.65/1.09    ! [X0,X1,X2] : (sP6(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(definition_folding,[],[f31,f43,f42])).
% 5.65/1.09  fof(f31,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(flattening,[],[f30])).
% 5.65/1.09  fof(f30,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.65/1.09    inference(ennf_transformation,[],[f12])).
% 5.65/1.09  fof(f12,axiom,(
% 5.65/1.09    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 5.65/1.09  fof(f10497,plain,(
% 5.65/1.09    ~spl18_1313 | spl18_1 | ~spl18_577 | ~spl18_1148),
% 5.65/1.09    inference(avatar_split_clause,[],[f10490,f8768,f4146,f135,f10494])).
% 5.65/1.09  fof(f135,plain,(
% 5.65/1.09    spl18_1 <=> sK9 = k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).
% 5.65/1.09  fof(f4146,plain,(
% 5.65/1.09    spl18_577 <=> k2_funct_1(sK10) = k4_relat_1(sK10)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_577])])).
% 5.65/1.09  fof(f8768,plain,(
% 5.65/1.09    spl18_1148 <=> sK9 = k1_funct_1(sK10,sK16(sK10,sK9))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1148])])).
% 5.65/1.09  fof(f10490,plain,(
% 5.65/1.09    ~sP5(sK16(sK10,sK9),sK9,k4_relat_1(sK10)) | (spl18_1 | ~spl18_577 | ~spl18_1148)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f8770,f5158])).
% 5.65/1.09  fof(f5158,plain,(
% 5.65/1.09    ( ! [X1] : (~sP5(X1,sK9,k4_relat_1(sK10)) | sK9 != k1_funct_1(sK10,X1)) ) | (spl18_1 | ~spl18_577)),
% 5.65/1.09    inference(backward_demodulation,[],[f2393,f4148])).
% 5.65/1.09  fof(f4148,plain,(
% 5.65/1.09    k2_funct_1(sK10) = k4_relat_1(sK10) | ~spl18_577),
% 5.65/1.09    inference(avatar_component_clause,[],[f4146])).
% 5.65/1.09  fof(f2393,plain,(
% 5.65/1.09    ( ! [X1] : (sK9 != k1_funct_1(sK10,X1) | ~sP5(X1,sK9,k2_funct_1(sK10))) ) | spl18_1),
% 5.65/1.09    inference(superposition,[],[f137,f117])).
% 5.65/1.09  fof(f137,plain,(
% 5.65/1.09    sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9)) | spl18_1),
% 5.65/1.09    inference(avatar_component_clause,[],[f135])).
% 5.65/1.09  fof(f8770,plain,(
% 5.65/1.09    sK9 = k1_funct_1(sK10,sK16(sK10,sK9)) | ~spl18_1148),
% 5.65/1.09    inference(avatar_component_clause,[],[f8768])).
% 5.65/1.09  fof(f8771,plain,(
% 5.65/1.09    spl18_1148 | ~spl18_1144),
% 5.65/1.09    inference(avatar_split_clause,[],[f8764,f8740,f8768])).
% 5.65/1.09  fof(f8740,plain,(
% 5.65/1.09    spl18_1144 <=> sP5(sK9,sK16(sK10,sK9),sK10)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1144])])).
% 5.65/1.09  fof(f8764,plain,(
% 5.65/1.09    sK9 = k1_funct_1(sK10,sK16(sK10,sK9)) | ~spl18_1144),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f8742,f117])).
% 5.65/1.09  fof(f8742,plain,(
% 5.65/1.09    sP5(sK9,sK16(sK10,sK9),sK10) | ~spl18_1144),
% 5.65/1.09    inference(avatar_component_clause,[],[f8740])).
% 5.65/1.09  fof(f8755,plain,(
% 5.65/1.09    spl18_1144 | ~spl18_5 | ~spl18_6 | ~spl18_1139),
% 5.65/1.09    inference(avatar_split_clause,[],[f8754,f8682,f159,f154,f8740])).
% 5.65/1.09  fof(f8682,plain,(
% 5.65/1.09    spl18_1139 <=> r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_1139])])).
% 5.65/1.09  fof(f8754,plain,(
% 5.65/1.09    sP5(sK9,sK16(sK10,sK9),sK10) | (~spl18_5 | ~spl18_6 | ~spl18_1139)),
% 5.65/1.09    inference(subsumption_resolution,[],[f8738,f1527])).
% 5.65/1.09  fof(f1527,plain,(
% 5.65/1.09    ( ! [X0,X1] : (sP6(sK10,X0,X1)) ) | (~spl18_5 | ~spl18_6)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f156,f119])).
% 5.65/1.09  fof(f8738,plain,(
% 5.65/1.09    sP5(sK9,sK16(sK10,sK9),sK10) | ~sP6(sK10,sK16(sK10,sK9),sK9) | ~spl18_1139),
% 5.65/1.09    inference(resolution,[],[f114,f8684])).
% 5.65/1.09  fof(f8684,plain,(
% 5.65/1.09    r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10) | ~spl18_1139),
% 5.65/1.09    inference(avatar_component_clause,[],[f8682])).
% 5.65/1.09  fof(f8709,plain,(
% 5.65/1.09    spl18_1141 | ~spl18_6 | ~spl18_1139),
% 5.65/1.09    inference(avatar_split_clause,[],[f8708,f8682,f159,f8699])).
% 5.65/1.09  fof(f8708,plain,(
% 5.65/1.09    r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10)) | (~spl18_6 | ~spl18_1139)),
% 5.65/1.09    inference(subsumption_resolution,[],[f8691,f161])).
% 5.65/1.09  fof(f8691,plain,(
% 5.65/1.09    r2_hidden(sK16(sK10,sK9),k1_relat_1(sK10)) | ~v1_relat_1(sK10) | ~spl18_1139),
% 5.65/1.09    inference(resolution,[],[f8684,f112])).
% 5.65/1.09  fof(f112,plain,(
% 5.65/1.09    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f29])).
% 5.65/1.09  fof(f29,plain,(
% 5.65/1.09    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(flattening,[],[f28])).
% 5.65/1.09  fof(f28,plain,(
% 5.65/1.09    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 5.65/1.09    inference(ennf_transformation,[],[f5])).
% 5.65/1.09  fof(f5,axiom,(
% 5.65/1.09    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 5.65/1.09  fof(f8707,plain,(
% 5.65/1.09    spl18_1142 | ~spl18_323 | ~spl18_1139),
% 5.65/1.09    inference(avatar_split_clause,[],[f8686,f8682,f2143,f8704])).
% 5.65/1.09  fof(f2143,plain,(
% 5.65/1.09    spl18_323 <=> sP0(sK10,k4_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_323])])).
% 5.65/1.09  fof(f8686,plain,(
% 5.65/1.09    r2_hidden(k4_tarski(sK9,sK16(sK10,sK9)),k4_relat_1(sK10)) | (~spl18_323 | ~spl18_1139)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f2145,f8684,f91])).
% 5.65/1.09  fof(f91,plain,(
% 5.65/1.09    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~sP0(X0,X1)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f55])).
% 5.65/1.09  fof(f55,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0) | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 5.65/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f53,f54])).
% 5.65/1.09  fof(f54,plain,(
% 5.65/1.09    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0) | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1))))),
% 5.65/1.09    introduced(choice_axiom,[])).
% 5.65/1.09  fof(f53,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 5.65/1.09    inference(rectify,[],[f52])).
% 5.65/1.09  fof(f52,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP0(X0,X1)))),
% 5.65/1.09    inference(nnf_transformation,[],[f34])).
% 5.65/1.09  fof(f34,plain,(
% 5.65/1.09    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 5.65/1.09  fof(f2145,plain,(
% 5.65/1.09    sP0(sK10,k4_relat_1(sK10)) | ~spl18_323),
% 5.65/1.09    inference(avatar_component_clause,[],[f2143])).
% 5.65/1.09  fof(f8685,plain,(
% 5.65/1.09    spl18_1139 | ~spl18_3),
% 5.65/1.09    inference(avatar_split_clause,[],[f8677,f144,f8682])).
% 5.65/1.09  fof(f144,plain,(
% 5.65/1.09    spl18_3 <=> r2_hidden(sK9,k2_relat_1(sK10))),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).
% 5.65/1.09  fof(f8677,plain,(
% 5.65/1.09    r2_hidden(k4_tarski(sK16(sK10,sK9),sK9),sK10) | ~spl18_3),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f130,f146,f106])).
% 5.65/1.09  fof(f106,plain,(
% 5.65/1.09    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK16(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | ~sP4(X0,X1)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f67])).
% 5.65/1.09  fof(f67,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP4(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK14(X0,X1)),X0) | ~r2_hidden(sK14(X0,X1),X1)) & (r2_hidden(k4_tarski(sK15(X0,X1),sK14(X0,X1)),X0) | r2_hidden(sK14(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK16(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | ~sP4(X0,X1)))),
% 5.65/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f63,f66,f65,f64])).
% 5.65/1.09  fof(f64,plain,(
% 5.65/1.09    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK14(X0,X1)),X0) | ~r2_hidden(sK14(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK14(X0,X1)),X0) | r2_hidden(sK14(X0,X1),X1))))),
% 5.65/1.09    introduced(choice_axiom,[])).
% 5.65/1.09  fof(f65,plain,(
% 5.65/1.09    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK14(X0,X1)),X0) => r2_hidden(k4_tarski(sK15(X0,X1),sK14(X0,X1)),X0))),
% 5.65/1.09    introduced(choice_axiom,[])).
% 5.65/1.09  fof(f66,plain,(
% 5.65/1.09    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK16(X0,X5),X5),X0))),
% 5.65/1.09    introduced(choice_axiom,[])).
% 5.65/1.09  fof(f63,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | ~sP4(X0,X1)))),
% 5.65/1.09    inference(rectify,[],[f62])).
% 5.65/1.09  fof(f62,plain,(
% 5.65/1.09    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | ~sP4(X0,X1)))),
% 5.65/1.09    inference(nnf_transformation,[],[f40])).
% 5.65/1.09  fof(f40,plain,(
% 5.65/1.09    ! [X0,X1] : (sP4(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 5.65/1.09  fof(f146,plain,(
% 5.65/1.09    r2_hidden(sK9,k2_relat_1(sK10)) | ~spl18_3),
% 5.65/1.09    inference(avatar_component_clause,[],[f144])).
% 5.65/1.09  fof(f130,plain,(
% 5.65/1.09    ( ! [X0] : (sP4(X0,k2_relat_1(X0))) )),
% 5.65/1.09    inference(equality_resolution,[],[f110])).
% 5.65/1.09  fof(f110,plain,(
% 5.65/1.09    ( ! [X0,X1] : (sP4(X0,X1) | k2_relat_1(X0) != X1) )),
% 5.65/1.09    inference(cnf_transformation,[],[f68])).
% 5.65/1.09  fof(f68,plain,(
% 5.65/1.09    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ~sP4(X0,X1)) & (sP4(X0,X1) | k2_relat_1(X0) != X1))),
% 5.65/1.09    inference(nnf_transformation,[],[f41])).
% 5.65/1.09  fof(f41,plain,(
% 5.65/1.09    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> sP4(X0,X1))),
% 5.65/1.09    inference(definition_folding,[],[f1,f40])).
% 5.65/1.09  fof(f1,axiom,(
% 5.65/1.09    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 5.65/1.09  fof(f7660,plain,(
% 5.65/1.09    spl18_952 | ~spl18_6 | ~spl18_7),
% 5.65/1.09    inference(avatar_split_clause,[],[f7573,f166,f159,f7657])).
% 5.65/1.09  fof(f7573,plain,(
% 5.65/1.09    k1_relat_1(k5_relat_1(k4_relat_1(sK10),sK10)) = k10_relat_1(k4_relat_1(sK10),k1_relat_1(sK10)) | (~spl18_6 | ~spl18_7)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f168,f161,f87])).
% 5.65/1.09  fof(f4173,plain,(
% 5.65/1.09    spl18_580 | ~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_118),
% 5.65/1.09    inference(avatar_split_clause,[],[f4168,f859,f159,f154,f149,f4170])).
% 5.65/1.09  fof(f4168,plain,(
% 5.65/1.09    v1_funct_1(k4_relat_1(sK10)) | (~spl18_4 | ~spl18_5 | ~spl18_6 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4167,f161])).
% 5.65/1.09  fof(f4167,plain,(
% 5.65/1.09    v1_funct_1(k4_relat_1(sK10)) | ~v1_relat_1(sK10) | (~spl18_4 | ~spl18_5 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4166,f156])).
% 5.65/1.09  fof(f4166,plain,(
% 5.65/1.09    v1_funct_1(k4_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl18_4 | ~spl18_118)),
% 5.65/1.09    inference(subsumption_resolution,[],[f3975,f151])).
% 5.65/1.09  fof(f3975,plain,(
% 5.65/1.09    v1_funct_1(k4_relat_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | ~spl18_118),
% 5.65/1.09    inference(superposition,[],[f861,f97])).
% 5.65/1.09  fof(f4165,plain,(
% 5.65/1.09    ~spl18_579 | spl18_2 | ~spl18_4 | ~spl18_5 | ~spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f4160,f159,f154,f149,f139,f4162])).
% 5.65/1.09  fof(f139,plain,(
% 5.65/1.09    spl18_2 <=> sK9 = k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).
% 5.65/1.09  fof(f4160,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) | (spl18_2 | ~spl18_4 | ~spl18_5 | ~spl18_6)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4159,f161])).
% 5.65/1.09  fof(f4159,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) | ~v1_relat_1(sK10) | (spl18_2 | ~spl18_4 | ~spl18_5)),
% 5.65/1.09    inference(subsumption_resolution,[],[f4158,f156])).
% 5.65/1.09  fof(f4158,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (spl18_2 | ~spl18_4)),
% 5.65/1.09    inference(subsumption_resolution,[],[f3948,f151])).
% 5.65/1.09  fof(f3948,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k4_relat_1(sK10),sK10),sK9) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | spl18_2),
% 5.65/1.09    inference(superposition,[],[f141,f97])).
% 5.65/1.09  fof(f141,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9) | spl18_2),
% 5.65/1.09    inference(avatar_component_clause,[],[f139])).
% 5.65/1.09  fof(f4149,plain,(
% 5.65/1.09    spl18_577 | ~spl18_4 | ~spl18_5 | ~spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f3946,f159,f154,f149,f4146])).
% 5.65/1.09  fof(f3946,plain,(
% 5.65/1.09    k2_funct_1(sK10) = k4_relat_1(sK10) | (~spl18_4 | ~spl18_5 | ~spl18_6)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f156,f151,f97])).
% 5.65/1.09  fof(f2147,plain,(
% 5.65/1.09    spl18_323 | ~spl18_70),
% 5.65/1.09    inference(avatar_split_clause,[],[f2128,f569,f2143])).
% 5.65/1.09  fof(f569,plain,(
% 5.65/1.09    spl18_70 <=> sP1(k4_relat_1(sK10),sK10)),
% 5.65/1.09    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).
% 5.65/1.09  fof(f2128,plain,(
% 5.65/1.09    sP0(sK10,k4_relat_1(sK10)) | ~spl18_70),
% 5.65/1.09    inference(resolution,[],[f126,f571])).
% 5.65/1.09  fof(f571,plain,(
% 5.65/1.09    sP1(k4_relat_1(sK10),sK10) | ~spl18_70),
% 5.65/1.09    inference(avatar_component_clause,[],[f569])).
% 5.65/1.09  fof(f126,plain,(
% 5.65/1.09    ( ! [X1] : (~sP1(k4_relat_1(X1),X1) | sP0(X1,k4_relat_1(X1))) )),
% 5.65/1.09    inference(equality_resolution,[],[f88])).
% 5.65/1.09  fof(f88,plain,(
% 5.65/1.09    ( ! [X0,X1] : (sP0(X1,X0) | k4_relat_1(X1) != X0 | ~sP1(X0,X1)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f51])).
% 5.65/1.09  fof(f51,plain,(
% 5.65/1.09    ! [X0,X1] : (((k4_relat_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k4_relat_1(X1) != X0)) | ~sP1(X0,X1))),
% 5.65/1.09    inference(rectify,[],[f50])).
% 5.65/1.09  fof(f50,plain,(
% 5.65/1.09    ! [X1,X0] : (((k4_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k4_relat_1(X0) != X1)) | ~sP1(X1,X0))),
% 5.65/1.09    inference(nnf_transformation,[],[f35])).
% 5.65/1.09  fof(f35,plain,(
% 5.65/1.09    ! [X1,X0] : ((k4_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 5.65/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 5.65/1.09  fof(f862,plain,(
% 5.65/1.09    spl18_118 | ~spl18_5 | ~spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f856,f159,f154,f859])).
% 5.65/1.09  fof(f856,plain,(
% 5.65/1.09    v1_funct_1(k2_funct_1(sK10)) | (~spl18_5 | ~spl18_6)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f156,f96])).
% 5.65/1.09  fof(f96,plain,(
% 5.65/1.09    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f21])).
% 5.65/1.09  fof(f21,plain,(
% 5.65/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.65/1.09    inference(flattening,[],[f20])).
% 5.65/1.09  fof(f20,plain,(
% 5.65/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.65/1.09    inference(ennf_transformation,[],[f7])).
% 5.65/1.09  fof(f7,axiom,(
% 5.65/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 5.65/1.09  fof(f619,plain,(
% 5.65/1.09    spl18_79 | ~spl18_5 | ~spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f613,f159,f154,f616])).
% 5.65/1.09  fof(f613,plain,(
% 5.65/1.09    v1_relat_1(k2_funct_1(sK10)) | (~spl18_5 | ~spl18_6)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f156,f95])).
% 5.65/1.09  fof(f95,plain,(
% 5.65/1.09    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f21])).
% 5.65/1.09  fof(f572,plain,(
% 5.65/1.09    spl18_70 | ~spl18_6 | ~spl18_7),
% 5.65/1.09    inference(avatar_split_clause,[],[f230,f166,f159,f569])).
% 5.65/1.09  fof(f230,plain,(
% 5.65/1.09    sP1(k4_relat_1(sK10),sK10) | (~spl18_6 | ~spl18_7)),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f168,f94])).
% 5.65/1.09  fof(f94,plain,(
% 5.65/1.09    ( ! [X0,X1] : (sP1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f36])).
% 5.65/1.09  fof(f36,plain,(
% 5.65/1.09    ! [X0] : (! [X1] : (sP1(X1,X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.65/1.09    inference(definition_folding,[],[f19,f35,f34])).
% 5.65/1.09  fof(f19,plain,(
% 5.65/1.09    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.65/1.09    inference(ennf_transformation,[],[f2])).
% 5.65/1.09  fof(f2,axiom,(
% 5.65/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 5.65/1.09  fof(f169,plain,(
% 5.65/1.09    spl18_7 | ~spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f163,f159,f166])).
% 5.65/1.09  fof(f163,plain,(
% 5.65/1.09    v1_relat_1(k4_relat_1(sK10)) | ~spl18_6),
% 5.65/1.09    inference(unit_resulting_resolution,[],[f161,f86])).
% 5.65/1.09  fof(f86,plain,(
% 5.65/1.09    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.65/1.09    inference(cnf_transformation,[],[f17])).
% 5.65/1.09  fof(f17,plain,(
% 5.65/1.09    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 5.65/1.09    inference(ennf_transformation,[],[f3])).
% 5.65/1.09  fof(f3,axiom,(
% 5.65/1.09    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 5.65/1.09  fof(f162,plain,(
% 5.65/1.09    spl18_6),
% 5.65/1.09    inference(avatar_split_clause,[],[f79,f159])).
% 5.65/1.09  fof(f79,plain,(
% 5.65/1.09    v1_relat_1(sK10)),
% 5.65/1.09    inference(cnf_transformation,[],[f49])).
% 5.65/1.09  fof(f49,plain,(
% 5.65/1.09    (sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9) | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))) & r2_hidden(sK9,k2_relat_1(sK10)) & v2_funct_1(sK10) & v1_funct_1(sK10) & v1_relat_1(sK10)),
% 5.65/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f16,f48])).
% 5.65/1.09  fof(f48,plain,(
% 5.65/1.09    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9) | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))) & r2_hidden(sK9,k2_relat_1(sK10)) & v2_funct_1(sK10) & v1_funct_1(sK10) & v1_relat_1(sK10))),
% 5.65/1.09    introduced(choice_axiom,[])).
% 5.65/1.09  fof(f16,plain,(
% 5.65/1.09    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 5.65/1.09    inference(flattening,[],[f15])).
% 5.65/1.09  fof(f15,plain,(
% 5.65/1.09    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 5.65/1.09    inference(ennf_transformation,[],[f14])).
% 5.65/1.09  fof(f14,negated_conjecture,(
% 5.65/1.09    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 5.65/1.09    inference(negated_conjecture,[],[f13])).
% 5.65/1.09  fof(f13,conjecture,(
% 5.65/1.09    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 5.65/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 5.65/1.09  fof(f157,plain,(
% 5.65/1.09    spl18_5),
% 5.65/1.09    inference(avatar_split_clause,[],[f80,f154])).
% 5.65/1.09  fof(f80,plain,(
% 5.65/1.09    v1_funct_1(sK10)),
% 5.65/1.09    inference(cnf_transformation,[],[f49])).
% 5.65/1.09  fof(f152,plain,(
% 5.65/1.09    spl18_4),
% 5.65/1.09    inference(avatar_split_clause,[],[f81,f149])).
% 5.65/1.09  fof(f81,plain,(
% 5.65/1.09    v2_funct_1(sK10)),
% 5.65/1.09    inference(cnf_transformation,[],[f49])).
% 5.65/1.09  fof(f147,plain,(
% 5.65/1.09    spl18_3),
% 5.65/1.09    inference(avatar_split_clause,[],[f82,f144])).
% 5.65/1.09  fof(f82,plain,(
% 5.65/1.09    r2_hidden(sK9,k2_relat_1(sK10))),
% 5.65/1.09    inference(cnf_transformation,[],[f49])).
% 5.65/1.09  fof(f142,plain,(
% 5.65/1.09    ~spl18_1 | ~spl18_2),
% 5.65/1.09    inference(avatar_split_clause,[],[f83,f139,f135])).
% 5.65/1.09  fof(f83,plain,(
% 5.65/1.09    sK9 != k1_funct_1(k5_relat_1(k2_funct_1(sK10),sK10),sK9) | sK9 != k1_funct_1(sK10,k1_funct_1(k2_funct_1(sK10),sK9))),
% 5.65/1.09    inference(cnf_transformation,[],[f49])).
% 5.65/1.09  % SZS output end Proof for theBenchmark
% 5.65/1.09  % (31690)------------------------------
% 5.65/1.09  % (31690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.09  % (31690)Termination reason: Refutation
% 5.65/1.09  
% 5.65/1.09  % (31690)Memory used [KB]: 20980
% 5.65/1.09  % (31690)Time elapsed: 0.609 s
% 5.65/1.09  % (31690)------------------------------
% 5.65/1.09  % (31690)------------------------------
% 5.65/1.09  % (31665)Success in time 0.729 s
%------------------------------------------------------------------------------
