%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 168 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :    6
%              Number of atoms          :  250 ( 397 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f978,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f74,f90,f106,f111,f138,f164,f450,f825,f826,f956,f963,f976,f977])).

fof(f977,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f976,plain,
    ( spl1_135
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f970,f161,f972])).

fof(f972,plain,
    ( spl1_135
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_135])])).

fof(f161,plain,
    ( spl1_20
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f970,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_20 ),
    inference(resolution,[],[f163,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f163,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f963,plain,
    ( ~ spl1_133
    | ~ spl1_11
    | spl1_131 ),
    inference(avatar_split_clause,[],[f958,f946,f103,f960])).

fof(f960,plain,
    ( spl1_133
  <=> v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_133])])).

fof(f103,plain,
    ( spl1_11
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f946,plain,
    ( spl1_131
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_131])])).

fof(f958,plain,
    ( ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_11
    | spl1_131 ),
    inference(unit_resulting_resolution,[],[f105,f948,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f948,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | spl1_131 ),
    inference(avatar_component_clause,[],[f946])).

fof(f105,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f956,plain,
    ( ~ spl1_131
    | spl1_2
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f941,f65,f45,f946])).

fof(f45,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f65,plain,
    ( spl1_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f941,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | spl1_2
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f47,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_6 ),
    inference(resolution,[],[f29,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f47,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f826,plain,
    ( k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f825,plain,
    ( spl1_122
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f819,f135,f821])).

fof(f821,plain,
    ( spl1_122
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_122])])).

fof(f135,plain,
    ( spl1_16
  <=> r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f819,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_16 ),
    inference(resolution,[],[f137,f30])).

fof(f137,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f450,plain,
    ( ~ spl1_60
    | spl1_9
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f445,f108,f86,f447])).

fof(f447,plain,
    ( spl1_60
  <=> v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_60])])).

fof(f86,plain,
    ( spl1_9
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f108,plain,
    ( spl1_12
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f445,plain,
    ( ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | spl1_9
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f88,f110,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f110,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f88,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f164,plain,
    ( spl1_20
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f159,f71,f55,f50,f161])).

fof(f50,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f55,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f71,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f159,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f150,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f150,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f52,f73,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f52,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f138,plain,
    ( spl1_16
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f133,f71,f60,f50,f135])).

fof(f60,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f133,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f118,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f118,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f73,f52,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f111,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f94,f71,f50,f108])).

fof(f94,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f73,f52,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f106,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f95,f71,f50,f103])).

fof(f95,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f52,f73,f33])).

fof(f90,plain,
    ( ~ spl1_9
    | spl1_1
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f81,f65,f41,f86])).

fof(f41,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f81,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | spl1_1
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f67,f43,f29])).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f74,plain,
    ( spl1_7
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f69,f65,f71])).

fof(f69,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f68,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f58,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f48,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f45,f41])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:19:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (7447)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (7445)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (7443)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (7462)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (7441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (7454)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (7445)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (7442)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (7442)Refutation not found, incomplete strategy% (7442)------------------------------
% 0.22/0.51  % (7442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7442)Memory used [KB]: 10490
% 0.22/0.51  % (7442)Time elapsed: 0.093 s
% 0.22/0.51  % (7442)------------------------------
% 0.22/0.51  % (7442)------------------------------
% 0.22/0.51  % (7439)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (7462)Refutation not found, incomplete strategy% (7462)------------------------------
% 0.22/0.51  % (7462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7446)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (7462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7462)Memory used [KB]: 10618
% 0.22/0.52  % (7462)Time elapsed: 0.054 s
% 0.22/0.52  % (7462)------------------------------
% 0.22/0.52  % (7462)------------------------------
% 0.22/0.52  % (7446)Refutation not found, incomplete strategy% (7446)------------------------------
% 0.22/0.52  % (7446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7446)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7461)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (7446)Memory used [KB]: 6012
% 0.22/0.52  % (7446)Time elapsed: 0.066 s
% 0.22/0.52  % (7446)------------------------------
% 0.22/0.52  % (7446)------------------------------
% 0.22/0.52  % (7459)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (7458)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (7452)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (7455)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (7444)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (7453)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (7449)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (7440)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (7457)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (7451)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (7450)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f978,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f74,f90,f106,f111,f138,f164,f450,f825,f826,f956,f963,f976,f977])).
% 0.22/0.53  fof(f977,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f976,plain,(
% 0.22/0.53    spl1_135 | ~spl1_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f970,f161,f972])).
% 0.22/0.53  fof(f972,plain,(
% 0.22/0.53    spl1_135 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_135])])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    spl1_20 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.22/0.53  fof(f970,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_20),
% 0.22/0.53    inference(resolution,[],[f163,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~spl1_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f161])).
% 0.22/0.53  fof(f963,plain,(
% 0.22/0.53    ~spl1_133 | ~spl1_11 | spl1_131),
% 0.22/0.53    inference(avatar_split_clause,[],[f958,f946,f103,f960])).
% 0.22/0.53  fof(f960,plain,(
% 0.22/0.53    spl1_133 <=> v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_133])])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl1_11 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.53  fof(f946,plain,(
% 0.22/0.53    spl1_131 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_131])])).
% 0.22/0.53  fof(f958,plain,(
% 0.22/0.53    ~v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_11 | spl1_131)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f105,f948,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.53  fof(f948,plain,(
% 0.22/0.53    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | spl1_131),
% 0.22/0.53    inference(avatar_component_clause,[],[f946])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f956,plain,(
% 0.22/0.53    ~spl1_131 | spl1_2 | ~spl1_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f941,f65,f45,f946])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl1_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.53  fof(f941,plain,(
% 0.22/0.53    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | (spl1_2 | ~spl1_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_6),
% 0.22/0.53    inference(resolution,[],[f29,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0) | ~spl1_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f45])).
% 0.22/0.53  fof(f826,plain,(
% 0.22/0.53    k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f825,plain,(
% 0.22/0.53    spl1_122 | ~spl1_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f819,f135,f821])).
% 0.22/0.53  fof(f821,plain,(
% 0.22/0.53    spl1_122 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_122])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl1_16 <=> r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.53  fof(f819,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_16),
% 0.22/0.53    inference(resolution,[],[f137,f30])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | ~spl1_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f450,plain,(
% 0.22/0.53    ~spl1_60 | spl1_9 | ~spl1_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f445,f108,f86,f447])).
% 0.22/0.53  fof(f447,plain,(
% 0.22/0.53    spl1_60 <=> v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_60])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl1_9 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl1_12 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.53  fof(f445,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (spl1_9 | ~spl1_12)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f88,f110,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | spl1_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    spl1_20 | ~spl1_3 | ~spl1_4 | ~spl1_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f159,f71,f55,f50,f161])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl1_3 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f150,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f55])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f73,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    v1_relat_1(k1_xboole_0) | ~spl1_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f50])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    spl1_16 | ~spl1_3 | ~spl1_5 | ~spl1_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f71,f60,f50,f135])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl1_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | (~spl1_3 | ~spl1_5 | ~spl1_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f118,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f52,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl1_12 | ~spl1_3 | ~spl1_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f94,f71,f50,f108])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f52,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl1_11 | ~spl1_3 | ~spl1_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f95,f71,f50,f103])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f73,f33])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~spl1_9 | spl1_1 | ~spl1_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f81,f65,f41,f86])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (spl1_1 | ~spl1_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f67,f43,f29])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl1_7 | ~spl1_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f69,f65,f71])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    v1_relat_1(k1_xboole_0) | ~spl1_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f67,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl1_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl1_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    spl1_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f55])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl1_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f50])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~spl1_1 | ~spl1_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f45,f41])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7445)------------------------------
% 0.22/0.53  % (7445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7445)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7445)Memory used [KB]: 11385
% 0.22/0.53  % (7445)Time elapsed: 0.099 s
% 0.22/0.53  % (7445)------------------------------
% 0.22/0.53  % (7445)------------------------------
% 0.22/0.53  % (7460)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (7437)Success in time 0.169 s
%------------------------------------------------------------------------------
