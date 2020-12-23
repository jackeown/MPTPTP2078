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
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 469 expanded)
%              Number of leaves         :   30 ( 149 expanded)
%              Depth                    :   25
%              Number of atoms          :  368 (1182 expanded)
%              Number of equality atoms :   78 ( 292 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2040,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2039,f945])).

fof(f945,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f936,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f936,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f274,f910])).

fof(f910,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f864,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f864,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f863,f144])).

fof(f144,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f143,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f143,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f139,f108])).

fof(f108,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f139,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f138,f61])).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f96,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(resolution,[],[f129,f61])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ) ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f863,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f862,f57])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f862,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f853,f58])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f853,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f65,f844])).

fof(f844,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f797,f59])).

fof(f59,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f797,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK1)
      | k1_xboole_0 = k6_subset_1(X5,sK1) ) ),
    inference(resolution,[],[f696,f66])).

fof(f696,plain,(
    ! [X5] :
      ( r1_tarski(k6_subset_1(X5,sK1),k1_xboole_0)
      | ~ r1_tarski(X5,sK1) ) ),
    inference(superposition,[],[f164,f686])).

fof(f686,plain,(
    sK1 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f676,f95])).

fof(f95,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f70,f72,f72])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f676,plain,(
    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) ),
    inference(superposition,[],[f563,f169])).

fof(f169,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f160,f66])).

fof(f160,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(X2,X2),X3) ),
    inference(resolution,[],[f99,f94])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f68,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f84,f69,f91])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f563,plain,(
    ! [X0] : sK1 = k3_tarski(k1_enumset1(sK1,sK1,k6_subset_1(sK0,X0))) ),
    inference(resolution,[],[f520,f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f322,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f322,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f104,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f91])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK7(X0,X1,X2))
        & r1_tarski(X2,sK7(X0,X1,X2))
        & r1_tarski(X0,sK7(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK7(X0,X1,X2))
        & r1_tarski(X2,sK7(X0,X1,X2))
        & r1_tarski(X0,sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f520,plain,(
    ! [X2] : r1_tarski(k6_subset_1(sK0,X2),sK1) ),
    inference(resolution,[],[f515,f161])).

fof(f161,plain,(
    ! [X4,X5] : r1_tarski(k6_subset_1(X4,X5),X4) ),
    inference(resolution,[],[f99,f124])).

fof(f124,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f94,f95])).

fof(f515,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK0)
      | r1_tarski(X4,sK1) ) ),
    inference(superposition,[],[f133,f489])).

fof(f489,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f310,f59])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f309,f105])).

fof(f309,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f102])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f91])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X2,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f98,f95])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f99,f95])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f274,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f100,f185])).

fof(f185,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f92,f58])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f63,f91])).

fof(f63,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f85,f91,f69])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2039,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2028,f60])).

fof(f60,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f2028,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f206,f1842])).

fof(f1842,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f1817,f276])).

fof(f276,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_relat_1(sK1))
      | r1_tarski(X3,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f98,f185])).

fof(f1817,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f94,f793])).

fof(f793,plain,(
    k2_relat_1(sK1) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f792,f489])).

fof(f792,plain,(
    k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f791,f95])).

fof(f791,plain,(
    k2_relat_1(k3_tarski(k1_enumset1(sK1,sK1,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f790,f95])).

fof(f790,plain,(
    k2_relat_1(k3_tarski(k1_enumset1(sK1,sK1,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0))) ),
    inference(resolution,[],[f271,f58])).

fof(f271,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(sK0))) ) ),
    inference(resolution,[],[f93,f57])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f91,f91])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f206,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f101,f184])).

fof(f184,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f92,f57])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:34:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (13288)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (13289)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (13312)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (13304)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.58  % (13287)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (13305)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.58  % (13312)Refutation not found, incomplete strategy% (13312)------------------------------
% 0.22/0.58  % (13312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (13297)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.58  % (13291)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.59  % (13312)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (13312)Memory used [KB]: 10746
% 1.56/0.59  % (13312)Time elapsed: 0.150 s
% 1.56/0.59  % (13312)------------------------------
% 1.56/0.59  % (13312)------------------------------
% 1.56/0.60  % (13298)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.60  % (13284)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.60  % (13283)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.60  % (13285)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.60  % (13286)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.61  % (13307)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.88/0.61  % (13313)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.88/0.61  % (13311)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.88/0.61  % (13294)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.88/0.62  % (13303)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.88/0.62  % (13299)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.88/0.62  % (13302)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.88/0.62  % (13299)Refutation not found, incomplete strategy% (13299)------------------------------
% 1.88/0.62  % (13299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (13299)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (13299)Memory used [KB]: 10618
% 1.88/0.62  % (13299)Time elapsed: 0.191 s
% 1.88/0.62  % (13299)------------------------------
% 1.88/0.62  % (13299)------------------------------
% 1.88/0.62  % (13296)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.88/0.62  % (13306)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.88/0.62  % (13295)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.88/0.62  % (13293)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.88/0.63  % (13290)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.88/0.63  % (13313)Refutation not found, incomplete strategy% (13313)------------------------------
% 1.88/0.63  % (13313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (13301)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.88/0.63  % (13313)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (13313)Memory used [KB]: 1663
% 1.88/0.63  % (13313)Time elapsed: 0.201 s
% 1.88/0.63  % (13313)------------------------------
% 1.88/0.63  % (13313)------------------------------
% 1.88/0.63  % (13293)Refutation not found, incomplete strategy% (13293)------------------------------
% 1.88/0.63  % (13293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (13310)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.88/0.64  % (13308)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.88/0.64  % (13292)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.88/0.64  % (13309)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.88/0.65  % (13293)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.65  
% 1.88/0.65  % (13293)Memory used [KB]: 10746
% 1.88/0.65  % (13293)Time elapsed: 0.203 s
% 1.88/0.65  % (13293)------------------------------
% 1.88/0.65  % (13293)------------------------------
% 2.23/0.73  % (13289)Refutation found. Thanks to Tanya!
% 2.23/0.73  % SZS status Theorem for theBenchmark
% 2.23/0.73  % SZS output start Proof for theBenchmark
% 2.23/0.73  fof(f2040,plain,(
% 2.23/0.73    $false),
% 2.23/0.73    inference(subsumption_resolution,[],[f2039,f945])).
% 2.23/0.73  fof(f945,plain,(
% 2.23/0.73    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(subsumption_resolution,[],[f936,f62])).
% 2.23/0.73  fof(f62,plain,(
% 2.23/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f6])).
% 2.23/0.73  fof(f6,axiom,(
% 2.23/0.73    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.23/0.73  fof(f936,plain,(
% 2.23/0.73    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(superposition,[],[f274,f910])).
% 2.23/0.73  fof(f910,plain,(
% 2.23/0.73    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.23/0.73    inference(resolution,[],[f864,f66])).
% 2.23/0.73  fof(f66,plain,(
% 2.23/0.73    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.23/0.73    inference(cnf_transformation,[],[f30])).
% 2.23/0.73  fof(f30,plain,(
% 2.23/0.73    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.23/0.73    inference(ennf_transformation,[],[f7])).
% 2.23/0.73  fof(f7,axiom,(
% 2.23/0.73    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.23/0.73  fof(f864,plain,(
% 2.23/0.73    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.23/0.73    inference(forward_demodulation,[],[f863,f144])).
% 2.23/0.73  fof(f144,plain,(
% 2.23/0.73    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.23/0.73    inference(resolution,[],[f143,f67])).
% 2.23/0.73  fof(f67,plain,(
% 2.23/0.73    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.23/0.73    inference(cnf_transformation,[],[f44])).
% 2.23/0.73  fof(f44,plain,(
% 2.23/0.73    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f43])).
% 2.23/0.73  fof(f43,plain,(
% 2.23/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f31,plain,(
% 2.23/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.23/0.73    inference(ennf_transformation,[],[f2])).
% 2.23/0.73  fof(f2,axiom,(
% 2.23/0.73    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.23/0.73  fof(f143,plain,(
% 2.23/0.73    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.23/0.73    inference(resolution,[],[f139,f108])).
% 2.23/0.73  fof(f108,plain,(
% 2.23/0.73    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.23/0.73    inference(equality_resolution,[],[f79])).
% 2.23/0.73  fof(f79,plain,(
% 2.23/0.73    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.23/0.73    inference(cnf_transformation,[],[f54])).
% 2.23/0.73  fof(f54,plain,(
% 2.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f53,f52,f51])).
% 2.23/0.73  fof(f51,plain,(
% 2.23/0.73    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f52,plain,(
% 2.23/0.73    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f53,plain,(
% 2.23/0.73    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f50,plain,(
% 2.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.23/0.73    inference(rectify,[],[f49])).
% 2.23/0.73  fof(f49,plain,(
% 2.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.23/0.73    inference(nnf_transformation,[],[f18])).
% 2.23/0.73  fof(f18,axiom,(
% 2.23/0.73    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.23/0.73  fof(f139,plain,(
% 2.23/0.73    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.23/0.73    inference(subsumption_resolution,[],[f138,f61])).
% 2.23/0.73  fof(f61,plain,(
% 2.23/0.73    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f10])).
% 2.23/0.73  fof(f10,axiom,(
% 2.23/0.73    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.23/0.73  fof(f138,plain,(
% 2.23/0.73    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 2.23/0.73    inference(superposition,[],[f96,f135])).
% 2.23/0.73  fof(f135,plain,(
% 2.23/0.73    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 2.23/0.73    inference(resolution,[],[f129,f61])).
% 2.23/0.73  fof(f129,plain,(
% 2.23/0.73    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.23/0.73    inference(resolution,[],[f96,f67])).
% 2.23/0.73  fof(f96,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f75,f90])).
% 2.23/0.73  fof(f90,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.23/0.73    inference(definition_unfolding,[],[f71,f72])).
% 2.23/0.73  fof(f72,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f14])).
% 2.23/0.73  fof(f14,axiom,(
% 2.23/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.23/0.73  fof(f71,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.23/0.73    inference(cnf_transformation,[],[f17])).
% 2.23/0.73  fof(f17,axiom,(
% 2.23/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.23/0.73  fof(f75,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.23/0.73    inference(cnf_transformation,[],[f46])).
% 2.23/0.73  fof(f46,plain,(
% 2.23/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).
% 2.23/0.73  fof(f45,plain,(
% 2.23/0.73    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f32,plain,(
% 2.23/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.23/0.73    inference(ennf_transformation,[],[f24])).
% 2.23/0.73  fof(f24,plain,(
% 2.23/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.23/0.73    inference(rectify,[],[f1])).
% 2.23/0.73  fof(f1,axiom,(
% 2.23/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.23/0.73  fof(f863,plain,(
% 2.23/0.73    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.23/0.73    inference(subsumption_resolution,[],[f862,f57])).
% 2.23/0.73  fof(f57,plain,(
% 2.23/0.73    v1_relat_1(sK0)),
% 2.23/0.73    inference(cnf_transformation,[],[f42])).
% 2.23/0.73  fof(f42,plain,(
% 2.23/0.73    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f41,f40])).
% 2.23/0.73  fof(f40,plain,(
% 2.23/0.73    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f41,plain,(
% 2.23/0.73    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f26,plain,(
% 2.23/0.73    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.23/0.73    inference(flattening,[],[f25])).
% 2.23/0.73  fof(f25,plain,(
% 2.23/0.73    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.23/0.73    inference(ennf_transformation,[],[f23])).
% 2.23/0.73  fof(f23,negated_conjecture,(
% 2.23/0.73    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.23/0.73    inference(negated_conjecture,[],[f22])).
% 2.23/0.73  fof(f22,conjecture,(
% 2.23/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 2.23/0.73  fof(f862,plain,(
% 2.23/0.73    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 2.23/0.73    inference(subsumption_resolution,[],[f853,f58])).
% 2.23/0.73  fof(f58,plain,(
% 2.23/0.73    v1_relat_1(sK1)),
% 2.23/0.73    inference(cnf_transformation,[],[f42])).
% 2.23/0.73  fof(f853,plain,(
% 2.23/0.73    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.23/0.73    inference(superposition,[],[f65,f844])).
% 2.23/0.73  fof(f844,plain,(
% 2.23/0.73    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.23/0.73    inference(resolution,[],[f797,f59])).
% 2.23/0.73  fof(f59,plain,(
% 2.23/0.73    r1_tarski(sK0,sK1)),
% 2.23/0.73    inference(cnf_transformation,[],[f42])).
% 2.23/0.73  fof(f797,plain,(
% 2.23/0.73    ( ! [X5] : (~r1_tarski(X5,sK1) | k1_xboole_0 = k6_subset_1(X5,sK1)) )),
% 2.23/0.73    inference(resolution,[],[f696,f66])).
% 2.23/0.73  fof(f696,plain,(
% 2.23/0.73    ( ! [X5] : (r1_tarski(k6_subset_1(X5,sK1),k1_xboole_0) | ~r1_tarski(X5,sK1)) )),
% 2.23/0.73    inference(superposition,[],[f164,f686])).
% 2.23/0.73  fof(f686,plain,(
% 2.23/0.73    sK1 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,sK1))),
% 2.23/0.73    inference(forward_demodulation,[],[f676,f95])).
% 2.23/0.73  fof(f95,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f70,f72,f72])).
% 2.23/0.73  fof(f70,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f13])).
% 2.23/0.73  fof(f13,axiom,(
% 2.23/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.23/0.73  fof(f676,plain,(
% 2.23/0.73    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0))),
% 2.23/0.73    inference(superposition,[],[f563,f169])).
% 2.23/0.73  fof(f169,plain,(
% 2.23/0.73    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 2.23/0.73    inference(resolution,[],[f160,f66])).
% 2.23/0.73  fof(f160,plain,(
% 2.23/0.73    ( ! [X2,X3] : (r1_tarski(k6_subset_1(X2,X2),X3)) )),
% 2.23/0.73    inference(resolution,[],[f99,f94])).
% 2.23/0.73  fof(f94,plain,(
% 2.23/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.23/0.73    inference(definition_unfolding,[],[f68,f91])).
% 2.23/0.73  fof(f91,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.23/0.73    inference(definition_unfolding,[],[f73,f72])).
% 2.23/0.73  fof(f73,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.23/0.73    inference(cnf_transformation,[],[f15])).
% 2.23/0.73  fof(f15,axiom,(
% 2.23/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.23/0.73  fof(f68,plain,(
% 2.23/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.23/0.73    inference(cnf_transformation,[],[f11])).
% 2.23/0.73  fof(f11,axiom,(
% 2.23/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.23/0.73  fof(f99,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f84,f69,f91])).
% 2.23/0.73  fof(f69,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f16])).
% 2.23/0.73  fof(f16,axiom,(
% 2.23/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.23/0.73  fof(f84,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.23/0.73    inference(cnf_transformation,[],[f34])).
% 2.23/0.73  fof(f34,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.23/0.73    inference(ennf_transformation,[],[f8])).
% 2.23/0.73  fof(f8,axiom,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.23/0.73  fof(f563,plain,(
% 2.23/0.73    ( ! [X0] : (sK1 = k3_tarski(k1_enumset1(sK1,sK1,k6_subset_1(sK0,X0)))) )),
% 2.23/0.73    inference(resolution,[],[f520,f323])).
% 2.23/0.73  fof(f323,plain,(
% 2.23/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0) )),
% 2.23/0.73    inference(subsumption_resolution,[],[f322,f105])).
% 2.23/0.73  fof(f105,plain,(
% 2.23/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.23/0.73    inference(equality_resolution,[],[f77])).
% 2.23/0.73  fof(f77,plain,(
% 2.23/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.23/0.73    inference(cnf_transformation,[],[f48])).
% 2.23/0.73  fof(f48,plain,(
% 2.23/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/0.73    inference(flattening,[],[f47])).
% 2.23/0.73  fof(f47,plain,(
% 2.23/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/0.73    inference(nnf_transformation,[],[f3])).
% 2.23/0.73  fof(f3,axiom,(
% 2.23/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.23/0.73  fof(f322,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.23/0.73    inference(duplicate_literal_removal,[],[f320])).
% 2.23/0.73  fof(f320,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.23/0.73    inference(resolution,[],[f104,f102])).
% 2.23/0.73  fof(f102,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f89,f91])).
% 2.23/0.73  fof(f89,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f56])).
% 2.23/0.73  fof(f56,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK7(X0,X1,X2)) & r1_tarski(X2,sK7(X0,X1,X2)) & r1_tarski(X0,sK7(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f55])).
% 2.23/0.73  fof(f55,plain,(
% 2.23/0.73    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK7(X0,X1,X2)) & r1_tarski(X2,sK7(X0,X1,X2)) & r1_tarski(X0,sK7(X0,X1,X2))))),
% 2.23/0.73    introduced(choice_axiom,[])).
% 2.23/0.73  fof(f39,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.23/0.73    inference(flattening,[],[f38])).
% 2.23/0.73  fof(f38,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.23/0.73    inference(ennf_transformation,[],[f5])).
% 2.23/0.73  fof(f5,axiom,(
% 2.23/0.73    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.23/0.73  fof(f104,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f87,f91])).
% 2.23/0.73  fof(f87,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f56])).
% 2.23/0.73  fof(f520,plain,(
% 2.23/0.73    ( ! [X2] : (r1_tarski(k6_subset_1(sK0,X2),sK1)) )),
% 2.23/0.73    inference(resolution,[],[f515,f161])).
% 2.23/0.73  fof(f161,plain,(
% 2.23/0.73    ( ! [X4,X5] : (r1_tarski(k6_subset_1(X4,X5),X4)) )),
% 2.23/0.73    inference(resolution,[],[f99,f124])).
% 2.23/0.73  fof(f124,plain,(
% 2.23/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.23/0.73    inference(superposition,[],[f94,f95])).
% 2.23/0.73  fof(f515,plain,(
% 2.23/0.73    ( ! [X4] : (~r1_tarski(X4,sK0) | r1_tarski(X4,sK1)) )),
% 2.23/0.73    inference(superposition,[],[f133,f489])).
% 2.23/0.73  fof(f489,plain,(
% 2.23/0.73    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.23/0.73    inference(resolution,[],[f310,f59])).
% 2.23/0.73  fof(f310,plain,(
% 2.23/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 2.23/0.73    inference(subsumption_resolution,[],[f309,f105])).
% 2.23/0.73  fof(f309,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(duplicate_literal_removal,[],[f307])).
% 2.23/0.73  fof(f307,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(resolution,[],[f103,f102])).
% 2.23/0.73  fof(f103,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X2,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f88,f91])).
% 2.23/0.73  fof(f88,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f56])).
% 2.23/0.73  fof(f133,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_tarski(X2,X1)) )),
% 2.23/0.73    inference(superposition,[],[f98,f95])).
% 2.23/0.73  fof(f98,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f83,f91])).
% 2.23/0.73  fof(f83,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f33])).
% 2.23/0.73  fof(f33,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.23/0.73    inference(ennf_transformation,[],[f4])).
% 2.23/0.73  fof(f4,axiom,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.23/0.73  fof(f164,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 2.23/0.73    inference(superposition,[],[f99,f95])).
% 2.23/0.73  fof(f65,plain,(
% 2.23/0.73    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f29])).
% 2.23/0.73  fof(f29,plain,(
% 2.23/0.73    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.73    inference(ennf_transformation,[],[f20])).
% 2.23/0.73  fof(f20,axiom,(
% 2.23/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 2.23/0.73  fof(f274,plain,(
% 2.23/0.73    ( ! [X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 2.23/0.73    inference(superposition,[],[f100,f185])).
% 2.23/0.73  fof(f185,plain,(
% 2.23/0.73    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.23/0.73    inference(resolution,[],[f92,f58])).
% 2.23/0.73  fof(f92,plain,(
% 2.23/0.73    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.23/0.73    inference(definition_unfolding,[],[f63,f91])).
% 2.23/0.73  fof(f63,plain,(
% 2.23/0.73    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f27])).
% 2.23/0.73  fof(f27,plain,(
% 2.23/0.73    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.23/0.73    inference(ennf_transformation,[],[f19])).
% 2.23/0.73  fof(f19,axiom,(
% 2.23/0.73    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.23/0.73  fof(f100,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f85,f91,f69])).
% 2.23/0.73  fof(f85,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f35])).
% 2.23/0.73  fof(f35,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.23/0.73    inference(ennf_transformation,[],[f9])).
% 2.23/0.73  fof(f9,axiom,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.23/0.73  fof(f2039,plain,(
% 2.23/0.73    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(subsumption_resolution,[],[f2028,f60])).
% 2.23/0.73  fof(f60,plain,(
% 2.23/0.73    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(cnf_transformation,[],[f42])).
% 2.23/0.73  fof(f2028,plain,(
% 2.23/0.73    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(resolution,[],[f206,f1842])).
% 2.23/0.73  fof(f1842,plain,(
% 2.23/0.73    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.23/0.73    inference(resolution,[],[f1817,f276])).
% 2.23/0.73  fof(f276,plain,(
% 2.23/0.73    ( ! [X3] : (~r1_tarski(X3,k2_relat_1(sK1)) | r1_tarski(X3,k3_relat_1(sK1))) )),
% 2.23/0.73    inference(superposition,[],[f98,f185])).
% 2.23/0.73  fof(f1817,plain,(
% 2.23/0.73    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.23/0.73    inference(superposition,[],[f94,f793])).
% 2.23/0.73  fof(f793,plain,(
% 2.23/0.73    k2_relat_1(sK1) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.23/0.73    inference(forward_demodulation,[],[f792,f489])).
% 2.23/0.73  fof(f792,plain,(
% 2.23/0.73    k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 2.23/0.73    inference(forward_demodulation,[],[f791,f95])).
% 2.23/0.73  fof(f791,plain,(
% 2.23/0.73    k2_relat_1(k3_tarski(k1_enumset1(sK1,sK1,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.23/0.73    inference(forward_demodulation,[],[f790,f95])).
% 2.23/0.73  fof(f790,plain,(
% 2.23/0.73    k2_relat_1(k3_tarski(k1_enumset1(sK1,sK1,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK0)))),
% 2.23/0.73    inference(resolution,[],[f271,f58])).
% 2.23/0.73  fof(f271,plain,(
% 2.23/0.73    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,sK0))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(sK0)))) )),
% 2.23/0.73    inference(resolution,[],[f93,f57])).
% 2.23/0.73  fof(f93,plain,(
% 2.23/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f64,f91,f91])).
% 2.23/0.73  fof(f64,plain,(
% 2.23/0.73    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f28])).
% 2.23/0.73  fof(f28,plain,(
% 2.23/0.73    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.73    inference(ennf_transformation,[],[f21])).
% 2.23/0.73  fof(f21,axiom,(
% 2.23/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 2.23/0.73  fof(f206,plain,(
% 2.23/0.73    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.23/0.73    inference(superposition,[],[f101,f184])).
% 2.23/0.73  fof(f184,plain,(
% 2.23/0.73    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.23/0.73    inference(resolution,[],[f92,f57])).
% 2.23/0.73  fof(f101,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(definition_unfolding,[],[f86,f91])).
% 2.23/0.73  fof(f86,plain,(
% 2.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.23/0.73    inference(cnf_transformation,[],[f37])).
% 2.23/0.73  fof(f37,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.23/0.73    inference(flattening,[],[f36])).
% 2.23/0.73  fof(f36,plain,(
% 2.23/0.73    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.23/0.73    inference(ennf_transformation,[],[f12])).
% 2.23/0.73  fof(f12,axiom,(
% 2.23/0.73    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.23/0.73  % SZS output end Proof for theBenchmark
% 2.23/0.73  % (13289)------------------------------
% 2.23/0.73  % (13289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.73  % (13289)Termination reason: Refutation
% 2.23/0.73  
% 2.23/0.73  % (13289)Memory used [KB]: 11897
% 2.23/0.73  % (13289)Time elapsed: 0.302 s
% 2.23/0.73  % (13289)------------------------------
% 2.23/0.73  % (13289)------------------------------
% 2.23/0.73  % (13282)Success in time 0.365 s
%------------------------------------------------------------------------------
