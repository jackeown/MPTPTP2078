%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:01 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 253 expanded)
%              Number of leaves         :   30 (  76 expanded)
%              Depth                    :   21
%              Number of atoms          :  325 ( 637 expanded)
%              Number of equality atoms :   92 ( 187 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f110,f159,f414,f740,f751,f774])).

fof(f774,plain,
    ( spl4_2
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | spl4_2
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f772,f83])).

fof(f83,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f772,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(resolution,[],[f739,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f739,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f737])).

fof(f737,plain,
    ( spl4_22
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f751,plain,
    ( ~ spl4_4
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl4_4
    | spl4_17 ),
    inference(subsumption_resolution,[],[f749,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f749,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl4_4
    | spl4_17 ),
    inference(subsumption_resolution,[],[f747,f108])).

fof(f108,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f747,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl4_17 ),
    inference(resolution,[],[f714,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f714,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl4_17
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f740,plain,
    ( ~ spl4_17
    | spl4_22
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f735,f107,f103,f737,f712])).

fof(f103,plain,
    ( spl4_3
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f735,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f734,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f734,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f691,f48])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f691,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f95,f678])).

fof(f678,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f677,f455])).

fof(f455,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f405,f44])).

fof(f405,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f402,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f402,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f401,f108])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f398])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f395,f63])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f334,f51])).

fof(f334,plain,
    ( ! [X4] :
        ( v1_xboole_0(k5_relat_1(k1_xboole_0,X4))
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X4))
        | ~ v1_relat_1(X4) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f328,f46])).

fof(f328,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X4))
        | v1_xboole_0(k5_relat_1(k1_xboole_0,X4))
        | ~ v1_relat_1(X4) )
    | ~ spl4_4 ),
    inference(superposition,[],[f58,f319])).

fof(f319,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f318,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f318,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f317,f108])).

fof(f317,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f312,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f312,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f677,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f668,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f668,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f588,f108])).

fof(f588,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k4_relat_1(k5_relat_1(sK0,k4_relat_1(X23))) = k5_relat_1(X23,k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f128,f44])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f125,f52])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(k4_relat_1(X0)))
      | v1_xboole_0(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f94,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_relat_1(k4_relat_1(X0)))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f91,f53])).

fof(f91,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f89,f52])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | v1_xboole_0(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f58,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f414,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f412,f79])).

fof(f79,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f412,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f402,f44])).

fof(f159,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f157,f112])).

fof(f112,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl4_4 ),
    inference(resolution,[],[f109,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f109,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f157,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f110,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f99,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f93,f48])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_relat_1(X0) ) ),
    inference(resolution,[],[f91,f51])).

fof(f84,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f81,f77])).

fof(f45,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (31446)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (31450)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (31457)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (31467)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (31459)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.56  % (31462)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (31466)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.56  % (31472)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.56  % (31454)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.57  % (31466)Refutation not found, incomplete strategy% (31466)------------------------------
% 1.41/0.57  % (31466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (31461)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.57  % (31466)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (31466)Memory used [KB]: 10618
% 1.41/0.57  % (31466)Time elapsed: 0.140 s
% 1.41/0.57  % (31466)------------------------------
% 1.41/0.57  % (31466)------------------------------
% 1.41/0.57  % (31465)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.58  % (31449)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.58  % (31470)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.58  % (31444)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.58  % (31445)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.59  % (31447)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.59  % (31468)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.59  % (31448)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.59  % (31456)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.59  % (31463)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.59  % (31471)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.60  % (31453)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.60  % (31461)Refutation not found, incomplete strategy% (31461)------------------------------
% 1.41/0.60  % (31461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (31461)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.60  
% 1.41/0.60  % (31461)Memory used [KB]: 10618
% 1.41/0.60  % (31461)Time elapsed: 0.174 s
% 1.41/0.60  % (31461)------------------------------
% 1.41/0.60  % (31461)------------------------------
% 1.41/0.60  % (31473)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.60  % (31455)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.60  % (31469)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.60  % (31460)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.61  % (31451)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.61  % (31458)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.61  % (31447)Refutation found. Thanks to Tanya!
% 1.41/0.61  % SZS status Theorem for theBenchmark
% 1.41/0.61  % SZS output start Proof for theBenchmark
% 1.41/0.62  fof(f775,plain,(
% 1.41/0.62    $false),
% 1.41/0.62    inference(avatar_sat_refutation,[],[f84,f110,f159,f414,f740,f751,f774])).
% 1.41/0.62  fof(f774,plain,(
% 1.41/0.62    spl4_2 | ~spl4_22),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f773])).
% 1.41/0.62  fof(f773,plain,(
% 1.41/0.62    $false | (spl4_2 | ~spl4_22)),
% 1.41/0.62    inference(subsumption_resolution,[],[f772,f83])).
% 1.41/0.62  fof(f83,plain,(
% 1.41/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl4_2),
% 1.41/0.62    inference(avatar_component_clause,[],[f81])).
% 1.41/0.62  fof(f81,plain,(
% 1.41/0.62    spl4_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.41/0.62  fof(f772,plain,(
% 1.41/0.62    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl4_22),
% 1.41/0.62    inference(resolution,[],[f739,f51])).
% 1.41/0.62  fof(f51,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.41/0.62    inference(cnf_transformation,[],[f24])).
% 1.41/0.62  fof(f24,plain,(
% 1.41/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f2])).
% 1.41/0.62  fof(f2,axiom,(
% 1.41/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.41/0.62  fof(f739,plain,(
% 1.41/0.62    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl4_22),
% 1.41/0.62    inference(avatar_component_clause,[],[f737])).
% 1.41/0.62  fof(f737,plain,(
% 1.41/0.62    spl4_22 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.41/0.62  fof(f751,plain,(
% 1.41/0.62    ~spl4_4 | spl4_17),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f750])).
% 1.41/0.62  fof(f750,plain,(
% 1.41/0.62    $false | (~spl4_4 | spl4_17)),
% 1.41/0.62    inference(subsumption_resolution,[],[f749,f44])).
% 1.41/0.62  fof(f44,plain,(
% 1.41/0.62    v1_relat_1(sK0)),
% 1.41/0.62    inference(cnf_transformation,[],[f38])).
% 1.41/0.62  fof(f38,plain,(
% 1.41/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.41/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).
% 1.41/0.62  fof(f37,plain,(
% 1.41/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f23,plain,(
% 1.41/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f22])).
% 1.41/0.62  fof(f22,negated_conjecture,(
% 1.41/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.41/0.62    inference(negated_conjecture,[],[f21])).
% 1.41/0.62  fof(f21,conjecture,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.41/0.62  fof(f749,plain,(
% 1.41/0.62    ~v1_relat_1(sK0) | (~spl4_4 | spl4_17)),
% 1.41/0.62    inference(subsumption_resolution,[],[f747,f108])).
% 1.41/0.62  fof(f108,plain,(
% 1.41/0.62    v1_relat_1(k1_xboole_0) | ~spl4_4),
% 1.41/0.62    inference(avatar_component_clause,[],[f107])).
% 1.41/0.62  fof(f107,plain,(
% 1.41/0.62    spl4_4 <=> v1_relat_1(k1_xboole_0)),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.41/0.62  fof(f747,plain,(
% 1.41/0.62    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl4_17),
% 1.41/0.62    inference(resolution,[],[f714,f63])).
% 1.41/0.62  fof(f63,plain,(
% 1.41/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f35])).
% 1.41/0.62  fof(f35,plain,(
% 1.41/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(flattening,[],[f34])).
% 1.41/0.62  fof(f34,plain,(
% 1.41/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f14])).
% 1.41/0.62  fof(f14,axiom,(
% 1.41/0.62    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.41/0.62  fof(f714,plain,(
% 1.41/0.62    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl4_17),
% 1.41/0.62    inference(avatar_component_clause,[],[f712])).
% 1.41/0.62  fof(f712,plain,(
% 1.41/0.62    spl4_17 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.41/0.62  fof(f740,plain,(
% 1.41/0.62    ~spl4_17 | spl4_22 | ~spl4_3 | ~spl4_4),
% 1.41/0.62    inference(avatar_split_clause,[],[f735,f107,f103,f737,f712])).
% 1.41/0.62  fof(f103,plain,(
% 1.41/0.62    spl4_3 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.41/0.62  fof(f735,plain,(
% 1.41/0.62    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.41/0.62    inference(subsumption_resolution,[],[f734,f46])).
% 1.41/0.62  fof(f46,plain,(
% 1.41/0.62    v1_xboole_0(k1_xboole_0)),
% 1.41/0.62    inference(cnf_transformation,[],[f1])).
% 1.41/0.62  fof(f1,axiom,(
% 1.41/0.62    v1_xboole_0(k1_xboole_0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.62  fof(f734,plain,(
% 1.41/0.62    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.41/0.62    inference(forward_demodulation,[],[f691,f48])).
% 1.41/0.62  fof(f48,plain,(
% 1.41/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.62    inference(cnf_transformation,[],[f20])).
% 1.41/0.62  fof(f20,axiom,(
% 1.41/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.41/0.62  fof(f691,plain,(
% 1.41/0.62    ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.41/0.62    inference(superposition,[],[f95,f678])).
% 1.41/0.62  fof(f678,plain,(
% 1.41/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.41/0.62    inference(forward_demodulation,[],[f677,f455])).
% 1.41/0.62  fof(f455,plain,(
% 1.41/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f405,f44])).
% 1.41/0.62  fof(f405,plain,(
% 1.41/0.62    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(X1))) ) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f402,f52])).
% 1.41/0.62  fof(f52,plain,(
% 1.41/0.62    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f25])).
% 1.41/0.62  fof(f25,plain,(
% 1.41/0.62    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f13])).
% 1.41/0.62  fof(f13,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.41/0.62  fof(f402,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl4_4),
% 1.41/0.62    inference(subsumption_resolution,[],[f401,f108])).
% 1.41/0.62  fof(f401,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_4),
% 1.41/0.62    inference(duplicate_literal_removal,[],[f398])).
% 1.41/0.62  fof(f398,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f395,f63])).
% 1.41/0.62  fof(f395,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f334,f51])).
% 1.41/0.62  fof(f334,plain,(
% 1.41/0.62    ( ! [X4] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X4)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X4)) | ~v1_relat_1(X4)) ) | ~spl4_4),
% 1.41/0.62    inference(subsumption_resolution,[],[f328,f46])).
% 1.41/0.62  fof(f328,plain,(
% 1.41/0.62    ( ! [X4] : (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X4)) | v1_xboole_0(k5_relat_1(k1_xboole_0,X4)) | ~v1_relat_1(X4)) ) | ~spl4_4),
% 1.41/0.62    inference(superposition,[],[f58,f319])).
% 1.41/0.62  fof(f319,plain,(
% 1.41/0.62    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | ~spl4_4),
% 1.41/0.62    inference(forward_demodulation,[],[f318,f47])).
% 1.41/0.62  fof(f47,plain,(
% 1.41/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.62    inference(cnf_transformation,[],[f20])).
% 1.41/0.62  fof(f318,plain,(
% 1.41/0.62    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | ~spl4_4),
% 1.41/0.62    inference(subsumption_resolution,[],[f317,f108])).
% 1.41/0.62  fof(f317,plain,(
% 1.41/0.62    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.41/0.62    inference(subsumption_resolution,[],[f312,f50])).
% 1.41/0.62  fof(f50,plain,(
% 1.41/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f3])).
% 1.41/0.62  fof(f3,axiom,(
% 1.41/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.62  fof(f312,plain,(
% 1.41/0.62    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.41/0.62    inference(superposition,[],[f57,f48])).
% 1.41/0.62  fof(f57,plain,(
% 1.41/0.62    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f30])).
% 1.41/0.62  fof(f30,plain,(
% 1.41/0.62    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(flattening,[],[f29])).
% 1.41/0.62  fof(f29,plain,(
% 1.41/0.62    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f18])).
% 1.41/0.62  fof(f18,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.41/0.62  fof(f58,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f32])).
% 1.41/0.62  fof(f32,plain,(
% 1.41/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.41/0.62    inference(flattening,[],[f31])).
% 1.41/0.62  fof(f31,plain,(
% 1.41/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f15])).
% 1.41/0.62  fof(f15,axiom,(
% 1.41/0.62    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.41/0.62  fof(f677,plain,(
% 1.41/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.41/0.62    inference(forward_demodulation,[],[f668,f105])).
% 1.41/0.62  fof(f105,plain,(
% 1.41/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl4_3),
% 1.41/0.62    inference(avatar_component_clause,[],[f103])).
% 1.41/0.62  fof(f668,plain,(
% 1.41/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f588,f108])).
% 1.41/0.62  fof(f588,plain,(
% 1.41/0.62    ( ! [X23] : (~v1_relat_1(X23) | k4_relat_1(k5_relat_1(sK0,k4_relat_1(X23))) = k5_relat_1(X23,k4_relat_1(sK0))) )),
% 1.41/0.62    inference(resolution,[],[f128,f44])).
% 1.41/0.62  fof(f128,plain,(
% 1.41/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(subsumption_resolution,[],[f125,f52])).
% 1.41/0.62  fof(f125,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(superposition,[],[f56,f53])).
% 1.41/0.62  fof(f53,plain,(
% 1.41/0.62    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f26])).
% 1.41/0.62  fof(f26,plain,(
% 1.41/0.62    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f16])).
% 1.41/0.62  fof(f16,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.41/0.62  fof(f56,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f28])).
% 1.41/0.62  fof(f28,plain,(
% 1.41/0.62    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f19])).
% 1.41/0.62  fof(f19,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.41/0.62  fof(f95,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_xboole_0(k2_relat_1(k4_relat_1(X0))) | v1_xboole_0(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(subsumption_resolution,[],[f94,f52])).
% 1.41/0.62  fof(f94,plain,(
% 1.41/0.62    ( ! [X0] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_relat_1(k4_relat_1(X0))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(superposition,[],[f91,f53])).
% 1.41/0.62  fof(f91,plain,(
% 1.41/0.62    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(subsumption_resolution,[],[f89,f52])).
% 1.41/0.62  fof(f89,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | v1_xboole_0(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(superposition,[],[f58,f54])).
% 1.41/0.62  fof(f54,plain,(
% 1.41/0.62    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f27])).
% 1.41/0.62  fof(f27,plain,(
% 1.41/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f17])).
% 1.41/0.62  fof(f17,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.41/0.62  fof(f414,plain,(
% 1.41/0.62    spl4_1 | ~spl4_4),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f413])).
% 1.41/0.62  fof(f413,plain,(
% 1.41/0.62    $false | (spl4_1 | ~spl4_4)),
% 1.41/0.62    inference(subsumption_resolution,[],[f412,f79])).
% 1.41/0.62  fof(f79,plain,(
% 1.41/0.62    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl4_1),
% 1.41/0.62    inference(avatar_component_clause,[],[f77])).
% 1.41/0.62  fof(f77,plain,(
% 1.41/0.62    spl4_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.41/0.62  fof(f412,plain,(
% 1.41/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl4_4),
% 1.41/0.62    inference(resolution,[],[f402,f44])).
% 1.41/0.62  fof(f159,plain,(
% 1.41/0.62    spl4_4),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f158])).
% 1.41/0.62  fof(f158,plain,(
% 1.41/0.62    $false | spl4_4),
% 1.41/0.62    inference(resolution,[],[f157,f112])).
% 1.41/0.62  fof(f112,plain,(
% 1.41/0.62    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl4_4),
% 1.41/0.62    inference(resolution,[],[f109,f60])).
% 1.41/0.62  fof(f60,plain,(
% 1.41/0.62    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f43])).
% 1.41/0.62  fof(f43,plain,(
% 1.41/0.62    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.41/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f42,f41])).
% 1.41/0.62  fof(f41,plain,(
% 1.41/0.62    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f42,plain,(
% 1.41/0.62    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f40,plain,(
% 1.41/0.62    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.41/0.62    inference(rectify,[],[f39])).
% 1.41/0.62  fof(f39,plain,(
% 1.41/0.62    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.41/0.62    inference(nnf_transformation,[],[f33])).
% 1.41/0.62  fof(f33,plain,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f12])).
% 1.41/0.62  fof(f12,axiom,(
% 1.41/0.62    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.41/0.62  fof(f109,plain,(
% 1.41/0.62    ~v1_relat_1(k1_xboole_0) | spl4_4),
% 1.41/0.62    inference(avatar_component_clause,[],[f107])).
% 1.41/0.62  fof(f157,plain,(
% 1.41/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.62    inference(resolution,[],[f75,f49])).
% 1.41/0.62  fof(f49,plain,(
% 1.41/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f4])).
% 1.41/0.62  fof(f4,axiom,(
% 1.41/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.41/0.62  fof(f75,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f65,f74])).
% 1.41/0.62  fof(f74,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f62,f73])).
% 1.41/0.62  fof(f73,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f64,f72])).
% 1.41/0.62  fof(f72,plain,(
% 1.41/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f66,f71])).
% 1.41/0.62  fof(f71,plain,(
% 1.41/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f67,f70])).
% 1.41/0.62  fof(f70,plain,(
% 1.41/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f68,f69])).
% 1.41/0.62  fof(f69,plain,(
% 1.41/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f10])).
% 1.41/0.62  fof(f10,axiom,(
% 1.41/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.41/0.62  fof(f68,plain,(
% 1.41/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f9])).
% 1.41/0.62  fof(f9,axiom,(
% 1.41/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.41/0.62  fof(f67,plain,(
% 1.41/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f8])).
% 1.41/0.62  fof(f8,axiom,(
% 1.41/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.41/0.62  fof(f66,plain,(
% 1.41/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f7])).
% 1.41/0.62  fof(f7,axiom,(
% 1.41/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.62  fof(f64,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f6])).
% 1.41/0.62  fof(f6,axiom,(
% 1.41/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.62  fof(f62,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f5])).
% 1.41/0.62  fof(f5,axiom,(
% 1.41/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.62  fof(f65,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f36,plain,(
% 1.41/0.62    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.41/0.62    inference(ennf_transformation,[],[f11])).
% 1.41/0.62  fof(f11,axiom,(
% 1.41/0.62    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.41/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.41/0.62  fof(f110,plain,(
% 1.41/0.62    spl4_3 | ~spl4_4),
% 1.41/0.62    inference(avatar_split_clause,[],[f101,f107,f103])).
% 1.41/0.62  fof(f101,plain,(
% 1.41/0.62    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.41/0.62    inference(subsumption_resolution,[],[f99,f46])).
% 1.41/0.62  fof(f99,plain,(
% 1.41/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.41/0.62    inference(superposition,[],[f93,f48])).
% 1.41/0.62  fof(f93,plain,(
% 1.41/0.62    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k4_relat_1(X0)) )),
% 1.41/0.62    inference(resolution,[],[f91,f51])).
% 1.41/0.62  fof(f84,plain,(
% 1.41/0.62    ~spl4_1 | ~spl4_2),
% 1.41/0.62    inference(avatar_split_clause,[],[f45,f81,f77])).
% 1.41/0.62  fof(f45,plain,(
% 1.41/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.41/0.62    inference(cnf_transformation,[],[f38])).
% 1.41/0.62  % SZS output end Proof for theBenchmark
% 1.41/0.62  % (31447)------------------------------
% 1.41/0.62  % (31447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.62  % (31447)Termination reason: Refutation
% 1.41/0.62  
% 1.41/0.62  % (31447)Memory used [KB]: 11001
% 1.41/0.62  % (31447)Time elapsed: 0.193 s
% 1.41/0.62  % (31447)------------------------------
% 1.41/0.62  % (31447)------------------------------
% 1.41/0.62  % (31443)Success in time 0.258 s
%------------------------------------------------------------------------------
