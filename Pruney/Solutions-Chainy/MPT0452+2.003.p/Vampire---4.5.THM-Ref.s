%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 959 expanded)
%              Number of leaves         :   10 ( 273 expanded)
%              Depth                    :   19
%              Number of atoms          :  249 (3558 expanded)
%              Number of equality atoms :   76 (1032 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f436,plain,(
    $false ),
    inference(subsumption_resolution,[],[f435,f427])).

fof(f427,plain,(
    r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f426,f22])).

fof(f22,plain,(
    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

fof(f426,plain,
    ( k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f425,f358])).

fof(f358,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f357,f175])).

fof(f175,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(X2,X3,X3),X2)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f163,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f163,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(X2,X3,X3),X3)
      | r2_hidden(sK1(X2,X3,X3),X2)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3 ) ),
    inference(factoring,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f357,plain,
    ( ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0))
    | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0))
    | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) ),
    inference(resolution,[],[f108,f175])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1,k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(X0,X1,k3_relat_1(k4_relat_1(sK0))),X0)
      | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(resolution,[],[f107,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(k4_relat_1(sK0)))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f106,f105])).

fof(f105,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | r2_hidden(X2,k3_relat_1(k4_relat_1(sK0))) ) ),
    inference(superposition,[],[f45,f102])).

fof(f102,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f101,f48])).

fof(f48,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f101,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f99,f50])).

fof(f50,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0)))) ),
    inference(resolution,[],[f73,f21])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(k4_relat_1(X0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(X0)),k1_relat_1(k4_relat_1(X0)),k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0)))) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f26,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(k4_relat_1(sK0)))
      | r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f104,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK0))
      | r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f47,f72])).

fof(f72,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f38,f21])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | r2_hidden(X1,k3_relat_1(k4_relat_1(sK0))) ) ),
    inference(superposition,[],[f46,f102])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f425,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f420,f176])).

fof(f176,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1(X4,X5,X4),X5)
      | k3_tarski(k2_enumset1(X4,X4,X4,X5)) = X4 ) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f164,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1(X4,X5,X4),X5)
      | r2_hidden(sK1(X4,X5,X4),X4)
      | k3_tarski(k2_enumset1(X4,X4,X4,X5)) = X4 ) ),
    inference(factoring,[],[f41])).

fof(f420,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))
    | k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f214,f91])).

fof(f91,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),k2_relat_1(sK0))
      | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X8,X8,X8,X9))
      | ~ r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),X9) ) ),
    inference(resolution,[],[f39,f76])).

fof(f76,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_relat_1(sK0))
      | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f45,f72])).

fof(f214,plain,(
    ! [X5] :
      ( r2_hidden(sK1(X5,k3_relat_1(k4_relat_1(sK0)),X5),k2_relat_1(sK0))
      | k3_tarski(k2_enumset1(X5,X5,X5,k3_relat_1(k4_relat_1(sK0)))) = X5
      | r2_hidden(sK1(X5,k3_relat_1(k4_relat_1(sK0)),X5),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f176,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(k4_relat_1(sK0)))
      | r2_hidden(X0,k2_relat_1(sK0))
      | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(superposition,[],[f47,f102])).

fof(f435,plain,(
    ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f424,f75])).

fof(f75,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_relat_1(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK0)) ) ),
    inference(superposition,[],[f46,f72])).

fof(f424,plain,(
    ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f423,f22])).

fof(f423,plain,
    ( k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f422,f358])).

fof(f422,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f421,f97])).

fof(f97,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK1(X10,X11,k3_relat_1(sK0)),k1_relat_1(sK0))
      | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X10,X10,X10,X11))
      | ~ r2_hidden(sK1(X10,X11,k3_relat_1(sK0)),X10) ) ),
    inference(resolution,[],[f40,f75])).

fof(f421,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,
    ( k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))
    | k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))
    | ~ r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f214,f96])).

fof(f96,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),k2_relat_1(sK0))
      | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X8,X8,X8,X9))
      | ~ r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),X8) ) ),
    inference(resolution,[],[f40,f76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31888)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (31880)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (31885)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (31887)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (31880)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f436,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f435,f427])).
% 0.20/0.52  fof(f427,plain,(
% 0.20/0.52    r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f426,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0)) & v1_relat_1(X0)) => (k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f425,f358])).
% 0.20/0.52  fof(f358,plain,(
% 0.20/0.52    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))),
% 0.20/0.52    inference(subsumption_resolution,[],[f357,f175])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r2_hidden(sK1(X2,X3,X3),X2) | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f163,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f34,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(rectify,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r2_hidden(sK1(X2,X3,X3),X3) | r2_hidden(sK1(X2,X3,X3),X2) | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3) )),
% 0.20/0.52    inference(factoring,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f37])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0)) | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f352])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0)) | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0))))),
% 0.20/0.52    inference(resolution,[],[f108,f175])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1,k3_relat_1(k4_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK1(X0,X1,k3_relat_1(k4_relat_1(sK0))),X0) | k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f107,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X0) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f37])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k3_relat_1(k4_relat_1(sK0))) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | r2_hidden(X2,k3_relat_1(k4_relat_1(sK0)))) )),
% 0.20/0.52    inference(superposition,[],[f45,f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK0)))),
% 0.20/0.52    inference(forward_demodulation,[],[f101,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f23,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    v1_relat_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)))),
% 0.20/0.52    inference(forward_demodulation,[],[f99,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f24,f21])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    k3_relat_1(k4_relat_1(sK0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))))),
% 0.20/0.52    inference(resolution,[],[f73,f21])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(k4_relat_1(X0)) = k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(X0)),k1_relat_1(k4_relat_1(X0)),k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))))) )),
% 0.20/0.52    inference(resolution,[],[f38,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f26,f37])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f29,f37])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k3_relat_1(k4_relat_1(sK0))) | r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f104,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.20/0.52    inference(superposition,[],[f47,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.20/0.52    inference(resolution,[],[f38,f21])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f37])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | r2_hidden(X1,k3_relat_1(k4_relat_1(sK0)))) )),
% 0.20/0.52    inference(superposition,[],[f46,f102])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f37])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f425,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f420,f176])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X4,X5] : (r2_hidden(sK1(X4,X5,X4),X5) | k3_tarski(k2_enumset1(X4,X4,X4,X5)) = X4) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f164,f40])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X4,X5] : (r2_hidden(sK1(X4,X5,X4),X5) | r2_hidden(sK1(X4,X5,X4),X4) | k3_tarski(k2_enumset1(X4,X4,X4,X5)) = X4) )),
% 0.20/0.52    inference(factoring,[],[f41])).
% 0.20/0.52  fof(f420,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0)))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f410])).
% 0.20/0.52  fof(f410,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) | k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(k4_relat_1(sK0)))),
% 0.20/0.52    inference(resolution,[],[f214,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X8,X9] : (~r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),k2_relat_1(sK0)) | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X8,X8,X8,X9)) | ~r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),X9)) )),
% 0.20/0.52    inference(resolution,[],[f39,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(X2,k3_relat_1(sK0)) | ~r2_hidden(X2,k2_relat_1(sK0))) )),
% 0.20/0.52    inference(superposition,[],[f45,f72])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    ( ! [X5] : (r2_hidden(sK1(X5,k3_relat_1(k4_relat_1(sK0)),X5),k2_relat_1(sK0)) | k3_tarski(k2_enumset1(X5,X5,X5,k3_relat_1(k4_relat_1(sK0)))) = X5 | r2_hidden(sK1(X5,k3_relat_1(k4_relat_1(sK0)),X5),k1_relat_1(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f176,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k4_relat_1(sK0))) | r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(X0,k1_relat_1(sK0))) )),
% 0.20/0.52    inference(superposition,[],[f47,f102])).
% 0.20/0.52  fof(f435,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f424,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(X1,k3_relat_1(sK0)) | ~r2_hidden(X1,k1_relat_1(sK0))) )),
% 0.20/0.52    inference(superposition,[],[f46,f72])).
% 0.20/0.52  fof(f424,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f423,f22])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f422,f358])).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f421,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X10,X11] : (~r2_hidden(sK1(X10,X11,k3_relat_1(sK0)),k1_relat_1(sK0)) | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X10,X10,X10,X11)) | ~r2_hidden(sK1(X10,X11,k3_relat_1(sK0)),X10)) )),
% 0.20/0.52    inference(resolution,[],[f40,f75])).
% 0.20/0.52  fof(f421,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f409])).
% 0.20/0.52  fof(f409,plain,(
% 0.20/0.52    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k1_relat_1(sK0)) | k3_relat_1(sK0) = k3_tarski(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)))) | ~r2_hidden(sK1(k3_relat_1(sK0),k3_relat_1(k4_relat_1(sK0)),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f214,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X8,X9] : (~r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),k2_relat_1(sK0)) | k3_relat_1(sK0) = k3_tarski(k2_enumset1(X8,X8,X8,X9)) | ~r2_hidden(sK1(X8,X9,k3_relat_1(sK0)),X8)) )),
% 0.20/0.52    inference(resolution,[],[f40,f76])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (31880)------------------------------
% 0.20/0.52  % (31880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31880)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (31880)Memory used [KB]: 6652
% 0.20/0.52  % (31880)Time elapsed: 0.053 s
% 0.20/0.52  % (31880)------------------------------
% 0.20/0.52  % (31880)------------------------------
% 0.20/0.53  % (31874)Success in time 0.169 s
%------------------------------------------------------------------------------
