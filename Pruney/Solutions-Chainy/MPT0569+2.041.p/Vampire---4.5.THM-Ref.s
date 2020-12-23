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
% DateTime   : Thu Dec  3 12:50:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 319 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   24
%              Number of atoms          :  326 (1323 expanded)
%              Number of equality atoms :   55 ( 257 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f199])).

fof(f199,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f49,f198])).

fof(f198,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f192,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f192,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f190,f47])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f190,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0)
      | ~ r2_hidden(X1,k10_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK0,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f89,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f243,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(resolution,[],[f231,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f231,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(X1,sK0),k2_relat_1(sK1))
      | r1_xboole_0(X1,sK0) ) ),
    inference(resolution,[],[f228,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f226,f52])).

fof(f226,plain,(
    r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(superposition,[],[f224,f85])).

fof(f85,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f224,plain,(
    ! [X0] : r1_xboole_0(sK0,k9_relat_1(sK1,X0)) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,k9_relat_1(sK1,X0))
      | r1_xboole_0(sK0,k9_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f210,f51])).

fof(f210,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(sK0,X1),k9_relat_1(sK1,X2))
      | r1_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f208,f50])).

fof(f208,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(subsumption_resolution,[],[f206,f95])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f82,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f82,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f67,f76,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f206,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,sK1),k1_xboole_0)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(superposition,[],[f203,f198])).

fof(f203,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK5(X3,X5,sK1),k10_relat_1(sK1,X4))
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k9_relat_1(sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f202,f175])).

fof(f175,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k2_relat_1(sK1))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(forward_demodulation,[],[f174,f85])).

fof(f174,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1)))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(subsumption_resolution,[],[f172,f47])).

fof(f172,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1)))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1)))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f144,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f144,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK5(X3,X4,sK1),X5)
      | r2_hidden(X3,k9_relat_1(sK1,X5))
      | ~ r2_hidden(X3,k9_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f142,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,sK1),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f83,f47])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k2_relat_1(sK1))
      | r2_hidden(sK5(X3,X5,sK1),k10_relat_1(sK1,X4))
      | ~ r2_hidden(X3,k9_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f200,f138])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(X2,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f56,f47])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11799)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (11815)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (11799)Refutation not found, incomplete strategy% (11799)------------------------------
% 0.22/0.52  % (11799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11801)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11799)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11799)Memory used [KB]: 10746
% 0.22/0.52  % (11799)Time elapsed: 0.091 s
% 0.22/0.52  % (11799)------------------------------
% 0.22/0.52  % (11799)------------------------------
% 0.22/0.52  % (11802)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (11823)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (11798)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (11812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (11797)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (11809)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (11805)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (11800)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (11820)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (11802)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f243,f199])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f49,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f193])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f192,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f190,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f18])).
% 0.22/0.54  fof(f18,conjecture,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f187])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0) | ~r2_hidden(X1,k10_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f90,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(rectify,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK3(X0,sK0,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f89,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f52,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.54    inference(resolution,[],[f55,f47])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f242])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    r1_xboole_0(k2_relat_1(sK1),sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(resolution,[],[f231,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(sK2(X1,sK0),k2_relat_1(sK1)) | r1_xboole_0(X1,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f228,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f226,f52])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.54    inference(superposition,[],[f224,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f59,f47])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(sK0,k9_relat_1(sK1,X0))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f221])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(sK0,k9_relat_1(sK1,X0)) | r1_xboole_0(sK0,k9_relat_1(sK1,X0))) )),
% 0.22/0.54    inference(resolution,[],[f210,f51])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,X1),k9_relat_1(sK1,X2)) | r1_xboole_0(sK0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f208,f50])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f206,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f82,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f61,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f69,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f71,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f72,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.22/0.54    inference(equality_resolution,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f67,f76,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f70,f74])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.54    inference(flattening,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,sK1),k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) )),
% 0.22/0.54    inference(superposition,[],[f203,f198])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (r2_hidden(sK5(X3,X5,sK1),k10_relat_1(sK1,X4)) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,k9_relat_1(sK1,X5))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f202,f175])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK1)) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f174,f85])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1))) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f172,f47])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1))) | ~r2_hidden(X2,k9_relat_1(sK1,X3)) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(X2,k9_relat_1(sK1,k1_relat_1(sK1))) | ~r2_hidden(X2,k9_relat_1(sK1,X3)) | ~r2_hidden(X2,k9_relat_1(sK1,X3)) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f144,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(rectify,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~r2_hidden(sK5(X3,X4,sK1),X5) | r2_hidden(X3,k9_relat_1(sK1,X5)) | ~r2_hidden(X3,k9_relat_1(sK1,X4))) )),
% 0.22/0.55    inference(resolution,[],[f142,f138])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.22/0.55    inference(resolution,[],[f63,f47])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k9_relat_1(sK1,X1))) )),
% 0.22/0.55    inference(resolution,[],[f83,f47])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f65,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r2_hidden(X3,k2_relat_1(sK1)) | r2_hidden(sK5(X3,X5,sK1),k10_relat_1(sK1,X4)) | ~r2_hidden(X3,k9_relat_1(sK1,X5))) )),
% 0.22/0.55    inference(resolution,[],[f200,f138])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X2,k10_relat_1(sK1,X1))) )),
% 0.22/0.55    inference(resolution,[],[f56,f47])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11802)------------------------------
% 0.22/0.55  % (11802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11802)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11802)Memory used [KB]: 6396
% 0.22/0.55  % (11802)Time elapsed: 0.121 s
% 0.22/0.55  % (11802)------------------------------
% 0.22/0.55  % (11802)------------------------------
% 0.22/0.55  % (11796)Success in time 0.18 s
%------------------------------------------------------------------------------
