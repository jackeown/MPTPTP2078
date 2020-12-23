%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:10 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 229 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 ( 810 expanded)
%              Number of equality atoms :   98 ( 269 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f118,f121,f621])).

fof(f621,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f619,f104])).

fof(f104,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f619,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(backward_demodulation,[],[f133,f605])).

fof(f605,plain,
    ( sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f82,f101,f146])).

fof(f146,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14),X14)
      | k5_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),k3_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13)) = X14
      | sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14) = X12 ) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f101,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f80,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f74,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,
    ( ~ r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f82,f101,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f119,f82])).

fof(f119,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f107,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f107,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f71,f105,f73])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f59,f103,f99])).

fof(f59,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f36,f57])).

fof(f29,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f103,f99])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f30,f36,f57])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30608)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (30624)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (30598)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.25/0.52  % (30613)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.52  % (30616)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.53  % (30597)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.53  % (30604)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.53  % (30620)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.53  % (30605)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.25/0.53  % (30612)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.25/0.54  % (30618)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.54  % (30603)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.54  % (30601)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (30599)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.54  % (30621)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.25/0.54  % (30612)Refutation not found, incomplete strategy% (30612)------------------------------
% 1.25/0.54  % (30612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (30612)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (30612)Memory used [KB]: 10618
% 1.25/0.54  % (30612)Time elapsed: 0.126 s
% 1.25/0.54  % (30612)------------------------------
% 1.25/0.54  % (30612)------------------------------
% 1.25/0.54  % (30610)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.54  % (30619)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.54  % (30613)Refutation not found, incomplete strategy% (30613)------------------------------
% 1.36/0.54  % (30613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (30613)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (30613)Memory used [KB]: 1663
% 1.36/0.54  % (30613)Time elapsed: 0.134 s
% 1.36/0.54  % (30613)------------------------------
% 1.36/0.54  % (30613)------------------------------
% 1.36/0.54  % (30611)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.55  % (30596)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.55  % (30625)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.55  % (30622)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (30625)Refutation not found, incomplete strategy% (30625)------------------------------
% 1.36/0.55  % (30625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (30625)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (30625)Memory used [KB]: 1663
% 1.36/0.55  % (30625)Time elapsed: 0.139 s
% 1.36/0.55  % (30625)------------------------------
% 1.36/0.55  % (30625)------------------------------
% 1.36/0.55  % (30617)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.55  % (30609)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.55  % (30615)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.55  % (30614)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.55  % (30600)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.56  % (30623)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.56  % (30602)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.56  % (30606)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.56  % (30610)Refutation not found, incomplete strategy% (30610)------------------------------
% 1.36/0.56  % (30610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (30610)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (30610)Memory used [KB]: 1663
% 1.36/0.56  % (30610)Time elapsed: 0.109 s
% 1.36/0.56  % (30610)------------------------------
% 1.36/0.56  % (30610)------------------------------
% 1.36/0.56  % (30607)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.56  % (30607)Refutation not found, incomplete strategy% (30607)------------------------------
% 1.36/0.56  % (30607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (30607)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (30607)Memory used [KB]: 6140
% 1.36/0.56  % (30607)Time elapsed: 0.158 s
% 1.36/0.56  % (30607)------------------------------
% 1.36/0.56  % (30607)------------------------------
% 1.36/0.57  % (30616)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f622,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(avatar_sat_refutation,[],[f106,f118,f121,f621])).
% 1.36/0.57  fof(f621,plain,(
% 1.36/0.57    spl4_1 | ~spl4_2),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f620])).
% 1.36/0.57  fof(f620,plain,(
% 1.36/0.57    $false | (spl4_1 | ~spl4_2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f619,f104])).
% 1.36/0.57  fof(f104,plain,(
% 1.36/0.57    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.36/0.57    inference(avatar_component_clause,[],[f103])).
% 1.36/0.57  fof(f103,plain,(
% 1.36/0.57    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.57  fof(f619,plain,(
% 1.36/0.57    ~r2_hidden(sK0,sK1) | spl4_1),
% 1.36/0.57    inference(backward_demodulation,[],[f133,f605])).
% 1.36/0.57  fof(f605,plain,(
% 1.36/0.57    sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl4_1),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f82,f101,f146])).
% 1.36/0.57  fof(f146,plain,(
% 1.36/0.57    ( ! [X14,X12,X13] : (r2_hidden(sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14),X14) | k5_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),k3_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13)) = X14 | sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14) = X12) )),
% 1.36/0.57    inference(resolution,[],[f66,f72])).
% 1.36/0.57  fof(f72,plain,(
% 1.36/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.36/0.57    inference(equality_resolution,[],[f63])).
% 1.36/0.57  fof(f63,plain,(
% 1.36/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.36/0.57    inference(definition_unfolding,[],[f37,f57])).
% 1.36/0.57  fof(f57,plain,(
% 1.36/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f33,f56])).
% 1.36/0.57  fof(f56,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f35,f55])).
% 1.36/0.57  fof(f55,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f41,f54])).
% 1.36/0.57  fof(f54,plain,(
% 1.36/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f48,f53])).
% 1.36/0.57  fof(f53,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f49,f52])).
% 1.36/0.57  fof(f52,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f50,f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f13])).
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.36/0.57  fof(f50,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f12])).
% 1.36/0.57  fof(f12,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.57  fof(f49,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f11])).
% 1.36/0.57  fof(f11,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.57  fof(f48,plain,(
% 1.36/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f10])).
% 1.36/0.57  fof(f10,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.57  fof(f41,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f9])).
% 1.36/0.57  fof(f9,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.57  fof(f35,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f8])).
% 1.36/0.57  fof(f8,axiom,(
% 1.36/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.57  fof(f33,plain,(
% 1.36/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f7])).
% 1.36/0.57  fof(f7,axiom,(
% 1.36/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.57  fof(f37,plain,(
% 1.36/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f23])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.36/0.57  fof(f22,plain,(
% 1.36/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.36/0.57    introduced(choice_axiom,[])).
% 1.36/0.57  fof(f21,plain,(
% 1.36/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.57    inference(rectify,[],[f20])).
% 1.36/0.57  fof(f20,plain,(
% 1.36/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.57    inference(nnf_transformation,[],[f6])).
% 1.36/0.57  fof(f6,axiom,(
% 1.36/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.36/0.57  fof(f66,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.36/0.57    inference(definition_unfolding,[],[f45,f36])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f3])).
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.57  fof(f45,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f28])).
% 1.36/0.57  fof(f28,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.36/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.36/0.57  fof(f27,plain,(
% 1.36/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.36/0.57    introduced(choice_axiom,[])).
% 1.36/0.57  fof(f26,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.36/0.57    inference(rectify,[],[f25])).
% 1.36/0.57  fof(f25,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.36/0.57    inference(flattening,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.36/0.57    inference(nnf_transformation,[],[f2])).
% 1.36/0.57  fof(f2,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.36/0.57  fof(f101,plain,(
% 1.36/0.57    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 1.36/0.57    inference(avatar_component_clause,[],[f99])).
% 1.36/0.57  fof(f99,plain,(
% 1.36/0.57    spl4_1 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.57  fof(f82,plain,(
% 1.36/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.57    inference(condensation,[],[f81])).
% 1.36/0.57  fof(f81,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f80,f32])).
% 1.36/0.57  fof(f32,plain,(
% 1.36/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f5])).
% 1.36/0.57  fof(f5,axiom,(
% 1.36/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.57  fof(f80,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.36/0.57    inference(superposition,[],[f74,f31])).
% 1.36/0.57  fof(f31,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f4])).
% 1.36/0.57  fof(f4,axiom,(
% 1.36/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.36/0.57  fof(f74,plain,(
% 1.36/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f68])).
% 1.36/0.57  fof(f68,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.36/0.57    inference(definition_unfolding,[],[f43,f36])).
% 1.36/0.57  fof(f43,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.36/0.57    inference(cnf_transformation,[],[f28])).
% 1.36/0.57  fof(f133,plain,(
% 1.36/0.57    ~r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | spl4_1),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f82,f101,f65])).
% 1.36/0.57  fof(f65,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f46,f36])).
% 1.36/0.57  fof(f46,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f28])).
% 1.36/0.57  fof(f121,plain,(
% 1.36/0.57    ~spl4_1 | spl4_2),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f120])).
% 1.36/0.57  fof(f120,plain,(
% 1.36/0.57    $false | (~spl4_1 | spl4_2)),
% 1.36/0.57    inference(subsumption_resolution,[],[f119,f82])).
% 1.36/0.57  fof(f119,plain,(
% 1.36/0.57    r2_hidden(sK0,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.36/0.57    inference(backward_demodulation,[],[f107,f100])).
% 1.36/0.57  fof(f100,plain,(
% 1.36/0.57    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl4_1),
% 1.36/0.57    inference(avatar_component_clause,[],[f99])).
% 1.36/0.57  fof(f107,plain,(
% 1.36/0.57    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | spl4_2),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f71,f105,f73])).
% 1.36/0.57  fof(f73,plain,(
% 1.36/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.36/0.57    inference(equality_resolution,[],[f67])).
% 1.36/0.57  fof(f67,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.36/0.57    inference(definition_unfolding,[],[f44,f36])).
% 1.36/0.57  fof(f44,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.36/0.57    inference(cnf_transformation,[],[f28])).
% 1.36/0.57  fof(f105,plain,(
% 1.36/0.57    ~r2_hidden(sK0,sK1) | spl4_2),
% 1.36/0.57    inference(avatar_component_clause,[],[f103])).
% 1.36/0.57  fof(f71,plain,(
% 1.36/0.57    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.36/0.57    inference(equality_resolution,[],[f70])).
% 1.36/0.57  fof(f70,plain,(
% 1.36/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.36/0.57    inference(equality_resolution,[],[f62])).
% 1.36/0.57  fof(f62,plain,(
% 1.36/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.36/0.57    inference(definition_unfolding,[],[f38,f57])).
% 1.36/0.57  fof(f38,plain,(
% 1.36/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f23])).
% 1.36/0.57  fof(f118,plain,(
% 1.36/0.57    spl4_1 | spl4_2),
% 1.36/0.57    inference(avatar_split_clause,[],[f59,f103,f99])).
% 1.36/0.57  fof(f59,plain,(
% 1.36/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.36/0.57    inference(definition_unfolding,[],[f29,f36,f57])).
% 1.36/0.57  fof(f29,plain,(
% 1.36/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.57    inference(cnf_transformation,[],[f19])).
% 1.36/0.57  fof(f19,plain,(
% 1.36/0.57    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.36/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 1.36/0.57  fof(f18,plain,(
% 1.36/0.57    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.36/0.57    introduced(choice_axiom,[])).
% 1.36/0.57  fof(f17,plain,(
% 1.36/0.57    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.36/0.57    inference(nnf_transformation,[],[f16])).
% 1.36/0.57  fof(f16,plain,(
% 1.36/0.57    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f15])).
% 1.36/0.57  fof(f15,negated_conjecture,(
% 1.36/0.57    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.36/0.57    inference(negated_conjecture,[],[f14])).
% 1.36/0.57  fof(f14,conjecture,(
% 1.36/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.36/0.57  fof(f106,plain,(
% 1.36/0.57    ~spl4_1 | ~spl4_2),
% 1.36/0.57    inference(avatar_split_clause,[],[f58,f103,f99])).
% 1.36/0.57  fof(f58,plain,(
% 1.36/0.57    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.36/0.57    inference(definition_unfolding,[],[f30,f36,f57])).
% 1.36/0.57  fof(f30,plain,(
% 1.36/0.57    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.57    inference(cnf_transformation,[],[f19])).
% 1.36/0.57  % SZS output end Proof for theBenchmark
% 1.36/0.57  % (30616)------------------------------
% 1.36/0.57  % (30616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (30616)Termination reason: Refutation
% 1.36/0.57  
% 1.36/0.57  % (30616)Memory used [KB]: 11257
% 1.36/0.57  % (30616)Time elapsed: 0.146 s
% 1.36/0.57  % (30616)------------------------------
% 1.36/0.57  % (30616)------------------------------
% 1.36/0.57  % (30595)Success in time 0.204 s
%------------------------------------------------------------------------------
