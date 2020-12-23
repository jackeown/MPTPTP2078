%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 799 expanded)
%              Number of leaves         :   33 ( 271 expanded)
%              Depth                    :   19
%              Number of atoms          :  280 (1298 expanded)
%              Number of equality atoms :  126 (1055 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f109,f325,f348,f475,f1202,f1514])).

fof(f1514,plain,
    ( spl5_2
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f1513])).

fof(f1513,plain,
    ( $false
    | spl5_2
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f1509,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1509,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f1080,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1080,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1079,plain,
    ( spl5_32
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1202,plain,
    ( spl5_32
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1201,f105,f92,f1079])).

fof(f92,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f105,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1201,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_1
    | spl5_4 ),
    inference(forward_demodulation,[],[f1200,f1037])).

fof(f1037,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f503,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f503,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f253,f93])).

fof(f93,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f253,plain,(
    sK2 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f173,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f173,plain,(
    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f166,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f166,plain,(
    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f122,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f122,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(superposition,[],[f90,f82])).

fof(f82,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f43,f78,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f77])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1200,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | ~ spl5_1
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f509,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f509,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_1
    | spl5_4 ),
    inference(backward_demodulation,[],[f276,f93])).

fof(f276,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f275,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f275,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f113,f129])).

fof(f129,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | ~ r1_tarski(sK1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) )
    | spl5_4 ),
    inference(superposition,[],[f115,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f78,f78])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f115,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k3_xboole_0(sK2,X0))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f114,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f114,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f110,f107])).

fof(f107,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f110,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f82,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f113,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f83,f82])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f475,plain,
    ( spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f474,f92,f154])).

fof(f154,plain,
    ( spl5_7
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f474,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl5_1 ),
    inference(forward_demodulation,[],[f473,f119])).

fof(f119,plain,(
    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f113,f62])).

fof(f473,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f472,f53])).

fof(f472,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f196,f58])).

fof(f196,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f143,f85])).

fof(f143,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f135,f94])).

fof(f94,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f135,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f119,f86])).

fof(f348,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f346,f105,f101])).

fof(f101,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f346,plain,
    ( k1_xboole_0 != sK1
    | spl5_4 ),
    inference(superposition,[],[f161,f48])).

fof(f161,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k1_xboole_0)
    | spl5_4 ),
    inference(forward_demodulation,[],[f159,f47])).

fof(f159,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f125,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl5_4 ),
    inference(superposition,[],[f115,f47])).

fof(f325,plain,
    ( spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f322,f154,f101])).

fof(f322,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f155,f50])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f109,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f81,f105,f92])).

fof(f81,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f78,f78])).

fof(f44,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f80,f105,f101])).

fof(f80,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f45,f78])).

fof(f45,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f79,f96,f92])).

fof(f79,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17441)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (17440)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (17448)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (17456)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (17448)Refutation not found, incomplete strategy% (17448)------------------------------
% 0.21/0.51  % (17448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17442)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (17448)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17448)Memory used [KB]: 10618
% 0.21/0.51  % (17448)Time elapsed: 0.111 s
% 0.21/0.51  % (17448)------------------------------
% 0.21/0.51  % (17448)------------------------------
% 0.21/0.52  % (17436)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (17435)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (17433)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (17450)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (17434)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (17437)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (17444)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (17451)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (17431)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (17445)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (17453)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (17460)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (17453)Refutation not found, incomplete strategy% (17453)------------------------------
% 1.36/0.54  % (17453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (17453)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (17453)Memory used [KB]: 10746
% 1.36/0.54  % (17453)Time elapsed: 0.103 s
% 1.36/0.54  % (17453)------------------------------
% 1.36/0.54  % (17453)------------------------------
% 1.36/0.54  % (17438)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (17458)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (17459)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (17447)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (17454)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (17449)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (17452)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (17439)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (17446)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (17446)Refutation not found, incomplete strategy% (17446)------------------------------
% 1.36/0.55  % (17446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (17446)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (17446)Memory used [KB]: 6140
% 1.36/0.55  % (17446)Time elapsed: 0.001 s
% 1.36/0.55  % (17446)------------------------------
% 1.36/0.55  % (17446)------------------------------
% 1.36/0.56  % (17457)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (17443)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (17455)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.57  % (17432)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.01/0.66  % (17461)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.34/0.67  % (17457)Refutation found. Thanks to Tanya!
% 2.34/0.67  % SZS status Theorem for theBenchmark
% 2.34/0.67  % SZS output start Proof for theBenchmark
% 2.34/0.67  fof(f1515,plain,(
% 2.34/0.67    $false),
% 2.34/0.67    inference(avatar_sat_refutation,[],[f99,f108,f109,f325,f348,f475,f1202,f1514])).
% 2.34/0.67  fof(f1514,plain,(
% 2.34/0.67    spl5_2 | ~spl5_32),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f1513])).
% 2.34/0.67  fof(f1513,plain,(
% 2.34/0.67    $false | (spl5_2 | ~spl5_32)),
% 2.34/0.67    inference(subsumption_resolution,[],[f1509,f98])).
% 2.34/0.67  fof(f98,plain,(
% 2.34/0.67    k1_xboole_0 != sK2 | spl5_2),
% 2.34/0.67    inference(avatar_component_clause,[],[f96])).
% 2.34/0.67  fof(f96,plain,(
% 2.34/0.67    spl5_2 <=> k1_xboole_0 = sK2),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.34/0.67  fof(f1509,plain,(
% 2.34/0.67    k1_xboole_0 = sK2 | ~spl5_32),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f1080,f50])).
% 2.34/0.67  fof(f50,plain,(
% 2.34/0.67    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.34/0.67    inference(cnf_transformation,[],[f39])).
% 2.34/0.67  fof(f39,plain,(
% 2.34/0.67    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.34/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 2.34/0.67  fof(f38,plain,(
% 2.34/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.34/0.67    introduced(choice_axiom,[])).
% 2.34/0.67  fof(f28,plain,(
% 2.34/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.34/0.67    inference(ennf_transformation,[],[f3])).
% 2.34/0.67  fof(f3,axiom,(
% 2.34/0.67    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.34/0.67  fof(f1080,plain,(
% 2.34/0.67    ( ! [X5] : (~r2_hidden(X5,sK2)) ) | ~spl5_32),
% 2.34/0.67    inference(avatar_component_clause,[],[f1079])).
% 2.34/0.67  fof(f1079,plain,(
% 2.34/0.67    spl5_32 <=> ! [X5] : ~r2_hidden(X5,sK2)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.34/0.67  fof(f1202,plain,(
% 2.34/0.67    spl5_32 | ~spl5_1 | spl5_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f1201,f105,f92,f1079])).
% 2.34/0.67  fof(f92,plain,(
% 2.34/0.67    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.34/0.67  fof(f105,plain,(
% 2.34/0.67    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.34/0.67  fof(f1201,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl5_1 | spl5_4)),
% 2.34/0.67    inference(forward_demodulation,[],[f1200,f1037])).
% 2.34/0.67  fof(f1037,plain,(
% 2.34/0.67    sK2 = k3_xboole_0(sK1,sK2) | ~spl5_1),
% 2.34/0.67    inference(superposition,[],[f503,f53])).
% 2.34/0.67  fof(f53,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f1])).
% 2.34/0.67  fof(f1,axiom,(
% 2.34/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.34/0.67  fof(f503,plain,(
% 2.34/0.67    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_1),
% 2.34/0.67    inference(backward_demodulation,[],[f253,f93])).
% 2.34/0.67  fof(f93,plain,(
% 2.34/0.67    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 2.34/0.67    inference(avatar_component_clause,[],[f92])).
% 2.34/0.67  fof(f253,plain,(
% 2.34/0.67    sK2 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f173,f62])).
% 2.34/0.67  fof(f62,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f33])).
% 2.34/0.67  fof(f33,plain,(
% 2.34/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.34/0.67    inference(ennf_transformation,[],[f9])).
% 2.34/0.67  fof(f9,axiom,(
% 2.34/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.34/0.67  fof(f173,plain,(
% 2.34/0.67    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.34/0.67    inference(forward_demodulation,[],[f166,f48])).
% 2.34/0.67  fof(f48,plain,(
% 2.34/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.34/0.67    inference(cnf_transformation,[],[f12])).
% 2.34/0.67  fof(f12,axiom,(
% 2.34/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.34/0.67  fof(f166,plain,(
% 2.34/0.67    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.34/0.67    inference(superposition,[],[f122,f47])).
% 2.34/0.67  fof(f47,plain,(
% 2.34/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f10])).
% 2.34/0.67  fof(f10,axiom,(
% 2.34/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.34/0.67  fof(f122,plain,(
% 2.34/0.67    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f84,f111])).
% 2.34/0.67  fof(f111,plain,(
% 2.34/0.67    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 2.34/0.67    inference(superposition,[],[f90,f82])).
% 2.34/0.67  fof(f82,plain,(
% 2.34/0.67    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.34/0.67    inference(definition_unfolding,[],[f43,f78,f77])).
% 2.34/0.67  fof(f77,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f54,f76])).
% 2.34/0.67  fof(f76,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f55,f75])).
% 2.34/0.67  fof(f75,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f65,f74])).
% 2.34/0.67  fof(f74,plain,(
% 2.34/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f68,f73])).
% 2.34/0.67  fof(f73,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f69,f72])).
% 2.34/0.67  fof(f72,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f70,f71])).
% 2.34/0.67  fof(f71,plain,(
% 2.34/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f20])).
% 2.34/0.67  fof(f20,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.34/0.67  fof(f70,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f19])).
% 2.34/0.67  fof(f19,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.34/0.67  fof(f69,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f18])).
% 2.34/0.67  fof(f18,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.34/0.67  fof(f68,plain,(
% 2.34/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f17])).
% 2.34/0.67  fof(f17,axiom,(
% 2.34/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.34/0.67  fof(f65,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f16])).
% 2.34/0.67  fof(f16,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.34/0.67  fof(f55,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f15])).
% 2.34/0.67  fof(f15,axiom,(
% 2.34/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.34/0.67  fof(f54,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f23])).
% 2.34/0.67  fof(f23,axiom,(
% 2.34/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.34/0.67  fof(f78,plain,(
% 2.34/0.67    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f49,f76])).
% 2.34/0.67  fof(f49,plain,(
% 2.34/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f14])).
% 2.34/0.67  fof(f14,axiom,(
% 2.34/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.34/0.67  fof(f43,plain,(
% 2.34/0.67    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.34/0.67    inference(cnf_transformation,[],[f37])).
% 2.34/0.67  fof(f37,plain,(
% 2.34/0.67    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.34/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f36])).
% 2.34/0.67  fof(f36,plain,(
% 2.34/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.34/0.67    introduced(choice_axiom,[])).
% 2.34/0.67  fof(f27,plain,(
% 2.34/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.34/0.67    inference(ennf_transformation,[],[f25])).
% 2.34/0.67  fof(f25,negated_conjecture,(
% 2.34/0.67    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.34/0.67    inference(negated_conjecture,[],[f24])).
% 2.34/0.67  fof(f24,conjecture,(
% 2.34/0.67    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.34/0.67  fof(f90,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f66,f77])).
% 2.34/0.67  fof(f66,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f34,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.34/0.67    inference(ennf_transformation,[],[f6])).
% 2.34/0.67  fof(f6,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.34/0.67  fof(f84,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f52,f56])).
% 2.34/0.67  fof(f56,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f5])).
% 2.34/0.67  fof(f5,axiom,(
% 2.34/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.34/0.67  fof(f52,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f11,axiom,(
% 2.34/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.34/0.67  fof(f1200,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) ) | (~spl5_1 | spl5_4)),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f509,f58])).
% 2.34/0.67  fof(f58,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f41])).
% 2.34/0.67  fof(f41,plain,(
% 2.34/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.34/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f40])).
% 2.34/0.67  fof(f40,plain,(
% 2.34/0.67    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.34/0.67    introduced(choice_axiom,[])).
% 2.34/0.67  fof(f29,plain,(
% 2.34/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.34/0.67    inference(ennf_transformation,[],[f26])).
% 2.34/0.67  fof(f26,plain,(
% 2.34/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.34/0.67    inference(rectify,[],[f2])).
% 2.34/0.67  fof(f2,axiom,(
% 2.34/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.34/0.67  fof(f509,plain,(
% 2.34/0.67    r1_xboole_0(sK1,sK2) | (~spl5_1 | spl5_4)),
% 2.34/0.67    inference(backward_demodulation,[],[f276,f93])).
% 2.34/0.67  fof(f276,plain,(
% 2.34/0.67    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | spl5_4),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f275,f85])).
% 2.34/0.67  fof(f85,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f59,f78])).
% 2.34/0.67  fof(f59,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f30])).
% 2.34/0.67  fof(f30,plain,(
% 2.34/0.67    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.34/0.67    inference(ennf_transformation,[],[f21])).
% 2.34/0.67  fof(f21,axiom,(
% 2.34/0.67    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.34/0.67  fof(f275,plain,(
% 2.34/0.67    ~r2_hidden(sK0,sK2) | spl5_4),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f113,f129])).
% 2.34/0.67  fof(f129,plain,(
% 2.34/0.67    ( ! [X3] : (~r2_hidden(X3,sK2) | ~r1_tarski(sK1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ) | spl5_4),
% 2.34/0.67    inference(superposition,[],[f115,f86])).
% 2.34/0.67  fof(f86,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f60,f78,f78])).
% 2.34/0.67  fof(f60,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f31])).
% 2.34/0.67  fof(f31,plain,(
% 2.34/0.67    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.34/0.67    inference(ennf_transformation,[],[f22])).
% 2.34/0.67  fof(f22,axiom,(
% 2.34/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 2.34/0.67  fof(f115,plain,(
% 2.34/0.67    ( ! [X0] : (~r1_tarski(sK1,k3_xboole_0(sK2,X0))) ) | spl5_4),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f114,f67])).
% 2.34/0.67  fof(f67,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f35])).
% 2.34/0.67  fof(f35,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.34/0.67    inference(ennf_transformation,[],[f8])).
% 2.34/0.67  fof(f8,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.34/0.67  fof(f114,plain,(
% 2.34/0.67    ~r1_tarski(sK1,sK2) | spl5_4),
% 2.34/0.67    inference(subsumption_resolution,[],[f110,f107])).
% 2.34/0.67  fof(f107,plain,(
% 2.34/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 2.34/0.67    inference(avatar_component_clause,[],[f105])).
% 2.34/0.67  fof(f110,plain,(
% 2.34/0.67    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.34/0.67    inference(superposition,[],[f82,f87])).
% 2.34/0.67  fof(f87,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(definition_unfolding,[],[f61,f77])).
% 2.34/0.67  fof(f61,plain,(
% 2.34/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f32])).
% 2.34/0.67  fof(f32,plain,(
% 2.34/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.34/0.67    inference(ennf_transformation,[],[f7])).
% 2.34/0.67  fof(f7,axiom,(
% 2.34/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.34/0.67  fof(f113,plain,(
% 2.34/0.67    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.34/0.67    inference(superposition,[],[f83,f82])).
% 2.34/0.67  fof(f83,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f51,f77])).
% 2.34/0.67  fof(f51,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f13])).
% 2.34/0.67  fof(f13,axiom,(
% 2.34/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.34/0.67  fof(f475,plain,(
% 2.34/0.67    spl5_7 | spl5_1),
% 2.34/0.67    inference(avatar_split_clause,[],[f474,f92,f154])).
% 2.34/0.67  fof(f154,plain,(
% 2.34/0.67    spl5_7 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.34/0.67  fof(f474,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl5_1),
% 2.34/0.67    inference(forward_demodulation,[],[f473,f119])).
% 2.34/0.67  fof(f119,plain,(
% 2.34/0.67    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f113,f62])).
% 2.34/0.67  fof(f473,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | spl5_1),
% 2.34/0.67    inference(forward_demodulation,[],[f472,f53])).
% 2.34/0.67  fof(f472,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ) | spl5_1),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f196,f58])).
% 2.34/0.67  fof(f196,plain,(
% 2.34/0.67    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl5_1),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f143,f85])).
% 2.34/0.67  fof(f143,plain,(
% 2.34/0.67    ~r2_hidden(sK0,sK1) | spl5_1),
% 2.34/0.67    inference(subsumption_resolution,[],[f135,f94])).
% 2.34/0.67  fof(f94,plain,(
% 2.34/0.67    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_1),
% 2.34/0.67    inference(avatar_component_clause,[],[f92])).
% 2.34/0.67  fof(f135,plain,(
% 2.34/0.67    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK1)),
% 2.34/0.67    inference(superposition,[],[f119,f86])).
% 2.34/0.67  fof(f348,plain,(
% 2.34/0.67    ~spl5_3 | spl5_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f346,f105,f101])).
% 2.34/0.67  fof(f101,plain,(
% 2.34/0.67    spl5_3 <=> k1_xboole_0 = sK1),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.34/0.67  fof(f346,plain,(
% 2.34/0.67    k1_xboole_0 != sK1 | spl5_4),
% 2.34/0.67    inference(superposition,[],[f161,f48])).
% 2.34/0.67  fof(f161,plain,(
% 2.34/0.67    k1_xboole_0 != k5_xboole_0(sK1,k1_xboole_0) | spl5_4),
% 2.34/0.67    inference(forward_demodulation,[],[f159,f47])).
% 2.34/0.67  fof(f159,plain,(
% 2.34/0.67    k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) | spl5_4),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f125,f89])).
% 2.34/0.67  fof(f89,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.34/0.67    inference(definition_unfolding,[],[f63,f56])).
% 2.34/0.67  fof(f63,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f42])).
% 2.34/0.67  fof(f42,plain,(
% 2.34/0.67    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.34/0.67    inference(nnf_transformation,[],[f4])).
% 2.34/0.67  fof(f4,axiom,(
% 2.34/0.67    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.34/0.67  fof(f125,plain,(
% 2.34/0.67    ~r1_tarski(sK1,k1_xboole_0) | spl5_4),
% 2.34/0.67    inference(superposition,[],[f115,f47])).
% 2.34/0.67  fof(f325,plain,(
% 2.34/0.67    spl5_3 | ~spl5_7),
% 2.34/0.67    inference(avatar_split_clause,[],[f322,f154,f101])).
% 2.34/0.67  fof(f322,plain,(
% 2.34/0.67    k1_xboole_0 = sK1 | ~spl5_7),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f155,f50])).
% 2.34/0.67  fof(f155,plain,(
% 2.34/0.67    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_7),
% 2.34/0.67    inference(avatar_component_clause,[],[f154])).
% 2.34/0.67  fof(f109,plain,(
% 2.34/0.67    ~spl5_1 | ~spl5_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f81,f105,f92])).
% 2.34/0.67  fof(f81,plain,(
% 2.34/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.34/0.67    inference(definition_unfolding,[],[f44,f78,f78])).
% 2.34/0.67  fof(f44,plain,(
% 2.34/0.67    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f37])).
% 2.34/0.67  fof(f108,plain,(
% 2.34/0.67    ~spl5_3 | ~spl5_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f80,f105,f101])).
% 2.34/0.67  fof(f80,plain,(
% 2.34/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.34/0.67    inference(definition_unfolding,[],[f45,f78])).
% 2.34/0.67  fof(f45,plain,(
% 2.34/0.67    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.34/0.67    inference(cnf_transformation,[],[f37])).
% 2.34/0.67  fof(f99,plain,(
% 2.34/0.67    ~spl5_1 | ~spl5_2),
% 2.34/0.67    inference(avatar_split_clause,[],[f79,f96,f92])).
% 2.34/0.67  fof(f79,plain,(
% 2.34/0.67    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.34/0.67    inference(definition_unfolding,[],[f46,f78])).
% 2.34/0.67  fof(f46,plain,(
% 2.34/0.67    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f37])).
% 2.34/0.67  % SZS output end Proof for theBenchmark
% 2.34/0.67  % (17457)------------------------------
% 2.34/0.67  % (17457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.67  % (17457)Termination reason: Refutation
% 2.34/0.67  
% 2.34/0.67  % (17457)Memory used [KB]: 11897
% 2.34/0.67  % (17457)Time elapsed: 0.250 s
% 2.34/0.67  % (17457)------------------------------
% 2.34/0.67  % (17457)------------------------------
% 2.34/0.67  % (17430)Success in time 0.307 s
%------------------------------------------------------------------------------
