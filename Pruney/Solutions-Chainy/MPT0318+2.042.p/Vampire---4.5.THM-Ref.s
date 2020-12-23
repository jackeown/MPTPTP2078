%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 214 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 ( 330 expanded)
%              Number of equality atoms :  106 ( 302 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f89,f98])).

fof(f98,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f95,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl2_1
    | spl2_2 ),
    inference(backward_demodulation,[],[f72,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f93,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(superposition,[],[f36,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) = X0 ),
    inference(definition_unfolding,[],[f28,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f84,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))
    | ~ spl2_2 ),
    inference(superposition,[],[f65,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f65,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(definition_unfolding,[],[f39,f56,f55,f56,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f74,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f57,f71,f67])).

fof(f57,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f27,f56,f56])).

fof(f27,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28986)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (28980)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (29002)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (28983)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (28988)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (28980)Refutation not found, incomplete strategy% (28980)------------------------------
% 0.20/0.50  % (28980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28980)Memory used [KB]: 1663
% 0.20/0.50  % (28980)Time elapsed: 0.091 s
% 0.20/0.50  % (28980)------------------------------
% 0.20/0.50  % (28980)------------------------------
% 0.20/0.51  % (28996)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (28981)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (29007)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (28993)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (28992)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (28988)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f74,f89,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ~spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    $false | (~spl2_1 | spl2_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f95,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (~spl2_1 | spl2_2)),
% 0.20/0.51    inference(backward_demodulation,[],[f72,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.20/0.51    inference(superposition,[],[f36,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl2_1 <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false | ~spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f28,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f34,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f33,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f43,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) | ~spl2_2),
% 0.20/0.51    inference(superposition,[],[f65,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f76,f26])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.20/0.51    inference(superposition,[],[f36,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f71])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.20/0.51    inference(equality_resolution,[],[f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f56,f55,f56,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f52])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f71,f67])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f56,f56])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.51  % (28988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28988)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28988)Memory used [KB]: 10746
% 0.20/0.51  % (28988)Time elapsed: 0.111 s
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.52  % (28979)Success in time 0.163 s
%------------------------------------------------------------------------------
