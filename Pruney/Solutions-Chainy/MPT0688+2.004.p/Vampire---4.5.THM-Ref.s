%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 141 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  173 ( 333 expanded)
%              Number of equality atoms :   52 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f148,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f148,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f147,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f124,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f124,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f123,f81])).

fof(f81,plain,(
    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ~ r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f37,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
        | ~ r2_hidden(X2,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k2_relat_1(sK1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
          | ~ r2_hidden(X2,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f123,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))))) ),
    inference(forward_demodulation,[],[f122,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f122,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_setfam_1(k3_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))))) ),
    inference(unit_resulting_resolution,[],[f85,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f85,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f35,f77,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f77,plain,(
    k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)) ) ),
    inference(definition_unfolding,[],[f36,f62])).

fof(f36,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:29:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.57  % (17453)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (17477)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (17469)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (17456)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (17470)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (17460)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (17453)Refutation not found, incomplete strategy% (17453)------------------------------
% 0.22/0.58  % (17453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (17453)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (17453)Memory used [KB]: 10618
% 0.22/0.58  % (17453)Time elapsed: 0.145 s
% 0.22/0.58  % (17453)------------------------------
% 0.22/0.58  % (17453)------------------------------
% 0.22/0.58  % (17457)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (17477)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % (17455)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (17462)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % (17466)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (17454)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.60  % (17451)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f154,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f38,f148,f68])).
% 0.22/0.60  fof(f68,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f55,f62])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.60    inference(definition_unfolding,[],[f39,f60])).
% 0.22/0.60  fof(f60,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.60    inference(definition_unfolding,[],[f41,f59])).
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.60    inference(definition_unfolding,[],[f57,f58])).
% 0.22/0.60  fof(f58,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,axiom,(
% 0.22/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.60  fof(f41,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.60  fof(f39,plain,(
% 0.22/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,axiom,(
% 0.22/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.60    inference(nnf_transformation,[],[f11])).
% 0.22/0.60  fof(f11,axiom,(
% 0.22/0.60    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.60  fof(f148,plain,(
% 0.22/0.60    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_xboole_0)),
% 0.22/0.60    inference(subsumption_resolution,[],[f147,f70])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.60    inference(equality_resolution,[],[f47])).
% 0.22/0.60  fof(f47,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.60    inference(flattening,[],[f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.60    inference(nnf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.60  fof(f147,plain,(
% 0.22/0.60    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_xboole_0) | ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.60    inference(superposition,[],[f124,f54])).
% 0.22/0.60  fof(f54,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.60    inference(nnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.60  fof(f124,plain,(
% 0.22/0.60    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))),
% 0.22/0.60    inference(forward_demodulation,[],[f123,f81])).
% 0.22/0.60  fof(f81,plain,(
% 0.22/0.60    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f73,f67])).
% 0.22/0.60  fof(f67,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.60    inference(definition_unfolding,[],[f56,f62])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f34])).
% 0.22/0.60  fof(f73,plain,(
% 0.22/0.60    ~r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f37,f52])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(rectify,[],[f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(nnf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.60    inference(cnf_transformation,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) & v1_relat_1(sK1)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) & v1_relat_1(sK1))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.22/0.60    inference(flattening,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.60    inference(negated_conjecture,[],[f14])).
% 0.22/0.60  fof(f14,conjecture,(
% 0.22/0.60    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.22/0.60  fof(f123,plain,(
% 0.22/0.60    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))))),
% 0.22/0.60    inference(forward_demodulation,[],[f122,f64])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f42,f61])).
% 0.22/0.60  fof(f61,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f40,f60])).
% 0.22/0.60  fof(f40,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f12])).
% 0.22/0.60  fof(f12,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.61  fof(f122,plain,(
% 0.22/0.61    r2_hidden(sK2(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))),k1_setfam_1(k3_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))))),
% 0.22/0.61    inference(unit_resulting_resolution,[],[f85,f66])).
% 0.22/0.61  fof(f66,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.61    inference(definition_unfolding,[],[f43,f61])).
% 0.22/0.61  fof(f43,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f25,plain,(
% 0.22/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f24])).
% 0.22/0.61  fof(f24,plain,(
% 0.22/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f19,plain,(
% 0.22/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.61    inference(ennf_transformation,[],[f16])).
% 0.22/0.61  fof(f16,plain,(
% 0.22/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.61    inference(rectify,[],[f2])).
% 0.22/0.61  fof(f2,axiom,(
% 0.22/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.61  fof(f85,plain,(
% 0.22/0.61    ~r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))),
% 0.22/0.61    inference(unit_resulting_resolution,[],[f35,f77,f46])).
% 0.22/0.61  fof(f46,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.61    inference(nnf_transformation,[],[f20])).
% 0.22/0.61  fof(f20,plain,(
% 0.22/0.61    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f13])).
% 0.22/0.61  fof(f13,axiom,(
% 0.22/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.61  fof(f77,plain,(
% 0.22/0.61    k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))),
% 0.22/0.61    inference(unit_resulting_resolution,[],[f72,f63])).
% 0.22/0.61  fof(f63,plain,(
% 0.22/0.61    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.22/0.61    inference(definition_unfolding,[],[f36,f62])).
% 0.22/0.61  fof(f36,plain,(
% 0.22/0.61    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f23])).
% 0.22/0.61  fof(f72,plain,(
% 0.22/0.61    r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)),
% 0.22/0.61    inference(unit_resulting_resolution,[],[f37,f51])).
% 0.22/0.61  fof(f51,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    v1_relat_1(sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f23])).
% 0.22/0.61  fof(f38,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f6])).
% 0.22/0.61  fof(f6,axiom,(
% 0.22/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (17477)------------------------------
% 0.22/0.61  % (17477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (17477)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (17477)Memory used [KB]: 10746
% 0.22/0.61  % (17477)Time elapsed: 0.152 s
% 0.22/0.61  % (17477)------------------------------
% 0.22/0.61  % (17477)------------------------------
% 0.22/0.61  % (17474)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.61  % (17450)Success in time 0.235 s
%------------------------------------------------------------------------------
