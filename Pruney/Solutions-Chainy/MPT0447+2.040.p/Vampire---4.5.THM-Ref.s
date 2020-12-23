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
% DateTime   : Thu Dec  3 12:47:14 EST 2020

% Result     : Theorem 3.92s
% Output     : Refutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 368 expanded)
%              Number of leaves         :   34 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  483 (1280 expanded)
%              Number of equality atoms :   65 ( 153 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5595,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5594,f2913])).

fof(f2913,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2905,f73])).

fof(f73,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f2905,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f479,f1141])).

fof(f1141,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f1124,f598])).

fof(f598,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f117,f328])).

fof(f328,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f76,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f87,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f76,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f106,f112])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1124,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f950,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f157,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f93,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f102,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f950,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f369,f888])).

fof(f888,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f864,f281])).

fof(f281,plain,(
    ! [X6] :
      ( r2_hidden(sK11(X6),X6)
      | k1_xboole_0 = k2_relat_1(X6) ) ),
    inference(resolution,[],[f274,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f274,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k2_relat_1(X8))
      | r2_hidden(sK11(X8),X8) ) ),
    inference(resolution,[],[f128,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK11(X1),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK11(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK11(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f35,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK11(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK11(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f128,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
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
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
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
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f864,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f859,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,sK3(X1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f90,f80])).

fof(f80,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK3(X0))
          | r2_tarski(X2,sK3(X0))
          | ~ r1_tarski(X2,sK3(X0)) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),sK3(X0))
          | ~ r2_hidden(X3,sK3(X0)) )
      & ! [X4,X5] :
          ( r2_hidden(X5,sK3(X0))
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( r2_hidden(k1_zfmisc_1(X3),X1)
              | ~ r2_hidden(X3,X1) )
          & ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r1_tarski(X5,X4)
              | ~ r2_hidden(X4,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK3(X0))
            | r2_tarski(X2,sK3(X0))
            | ~ r1_tarski(X2,sK3(X0)) )
        & ! [X3] :
            ( r2_hidden(k1_zfmisc_1(X3),sK3(X0))
            | ~ r2_hidden(X3,sK3(X0)) )
        & ! [X5,X4] :
            ( r2_hidden(X5,sK3(X0))
            | ~ r1_tarski(X5,X4)
            | ~ r2_hidden(X4,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f859,plain,(
    ! [X4] : r1_xboole_0(k1_xboole_0,X4) ),
    inference(resolution,[],[f855,f74])).

fof(f74,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f855,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f850])).

fof(f850,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f151,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f151,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(sK4(X8,X9),X7)
      | ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f369,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f368,f70])).

fof(f70,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f368,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f362,f71])).

fof(f362,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f77,f136])).

fof(f136,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f85])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f479,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f119,f327])).

fof(f327,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f113,f70])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f108,f112])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f5594,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f5522,f1093])).

fof(f1093,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f933,f163])).

fof(f933,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f400,f885])).

fof(f885,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f864,f250])).

fof(f250,plain,(
    ! [X4] :
      ( r2_hidden(sK11(X4),X4)
      | k1_xboole_0 = k1_relat_1(X4) ) ),
    inference(resolution,[],[f245,f79])).

fof(f245,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k1_relat_1(X8))
      | r2_hidden(sK11(X8),X8) ) ),
    inference(resolution,[],[f126,f104])).

fof(f126,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f54,f57,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f400,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f399,f70])).

fof(f399,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f393,f71])).

fof(f393,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f78,f136])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f5522,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f117,f808])).

fof(f808,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k1_relat_1(sK1))) ),
    inference(resolution,[],[f616,f600])).

fof(f600,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f114,f328])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f84,f112])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f616,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f615,f123])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f615,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f612])).

fof(f612,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f122,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK12(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f111,f112])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK12(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK12(X0,X1,X2))
        & r1_tarski(X2,sK12(X0,X1,X2))
        & r1_tarski(X0,sK12(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f41,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK12(X0,X1,X2))
        & r1_tarski(X2,sK12(X0,X1,X2))
        & r1_tarski(X0,sK12(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK12(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f109,f112])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK12(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:37:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.30/0.53  % (12818)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.55  % (12823)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.55  % (12824)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.55  % (12832)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.56  % (12833)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.56  % (12821)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.56  % (12816)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.56  % (12835)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.56  % (12825)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.56  % (12827)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.57  % (12811)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.57  % (12813)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.57  % (12815)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.57  % (12817)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.58  % (12820)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.58  % (12826)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.58  % (12837)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.58  % (12810)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.58  % (12814)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.58  % (12812)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.58  % (12819)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.59  % (12830)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.59  % (12834)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.59  % (12831)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.59  % (12829)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.59  % (12838)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.59  % (12838)Refutation not found, incomplete strategy% (12838)------------------------------
% 1.30/0.59  % (12838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.59  % (12838)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.59  
% 1.30/0.59  % (12838)Memory used [KB]: 10746
% 1.30/0.59  % (12838)Time elapsed: 0.172 s
% 1.30/0.59  % (12838)------------------------------
% 1.30/0.59  % (12838)------------------------------
% 1.30/0.60  % (12839)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.60  % (12822)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.60  % (12839)Refutation not found, incomplete strategy% (12839)------------------------------
% 1.30/0.60  % (12839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.60  % (12839)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.60  
% 1.30/0.60  % (12839)Memory used [KB]: 1663
% 1.30/0.60  % (12839)Time elapsed: 0.179 s
% 1.30/0.60  % (12839)------------------------------
% 1.30/0.60  % (12839)------------------------------
% 1.30/0.60  % (12828)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.60  % (12820)Refutation not found, incomplete strategy% (12820)------------------------------
% 1.30/0.60  % (12820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.60  % (12820)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.60  
% 1.30/0.60  % (12820)Memory used [KB]: 10746
% 1.30/0.60  % (12820)Time elapsed: 0.158 s
% 1.30/0.60  % (12820)------------------------------
% 1.30/0.60  % (12820)------------------------------
% 1.30/0.60  % (12826)Refutation not found, incomplete strategy% (12826)------------------------------
% 1.30/0.60  % (12826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.60  % (12826)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.60  
% 1.30/0.60  % (12826)Memory used [KB]: 10746
% 1.30/0.60  % (12826)Time elapsed: 0.176 s
% 1.30/0.60  % (12826)------------------------------
% 1.30/0.60  % (12826)------------------------------
% 1.30/0.61  % (12836)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.56/0.73  % (12871)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.56/0.74  % (12873)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.56/0.74  % (12873)Refutation not found, incomplete strategy% (12873)------------------------------
% 2.56/0.74  % (12873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.56/0.74  % (12873)Termination reason: Refutation not found, incomplete strategy
% 2.56/0.74  
% 2.56/0.74  % (12873)Memory used [KB]: 6140
% 2.56/0.74  % (12873)Time elapsed: 0.111 s
% 2.56/0.74  % (12873)------------------------------
% 2.56/0.74  % (12873)------------------------------
% 2.56/0.75  % (12872)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.06/0.77  % (12813)Refutation not found, incomplete strategy% (12813)------------------------------
% 3.06/0.77  % (12813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.77  % (12813)Termination reason: Refutation not found, incomplete strategy
% 3.06/0.77  
% 3.06/0.77  % (12813)Memory used [KB]: 6140
% 3.06/0.77  % (12813)Time elapsed: 0.349 s
% 3.06/0.77  % (12813)------------------------------
% 3.06/0.77  % (12813)------------------------------
% 3.06/0.78  % (12874)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.06/0.84  % (12834)Time limit reached!
% 3.06/0.84  % (12834)------------------------------
% 3.06/0.84  % (12834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.84  % (12834)Termination reason: Time limit
% 3.06/0.84  
% 3.06/0.84  % (12834)Memory used [KB]: 13048
% 3.06/0.84  % (12834)Time elapsed: 0.415 s
% 3.06/0.84  % (12834)------------------------------
% 3.06/0.84  % (12834)------------------------------
% 3.06/0.85  % (12812)Time limit reached!
% 3.06/0.85  % (12812)------------------------------
% 3.06/0.85  % (12812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.85  % (12812)Termination reason: Time limit
% 3.06/0.85  
% 3.06/0.85  % (12812)Memory used [KB]: 6652
% 3.06/0.85  % (12812)Time elapsed: 0.424 s
% 3.06/0.85  % (12812)------------------------------
% 3.06/0.85  % (12812)------------------------------
% 3.77/0.88  % (12875)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.92/0.90  % (12876)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.92/0.91  % (12816)Refutation found. Thanks to Tanya!
% 3.92/0.91  % SZS status Theorem for theBenchmark
% 3.92/0.91  % SZS output start Proof for theBenchmark
% 3.92/0.91  fof(f5595,plain,(
% 3.92/0.91    $false),
% 3.92/0.91    inference(subsumption_resolution,[],[f5594,f2913])).
% 3.92/0.91  fof(f2913,plain,(
% 3.92/0.91    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.92/0.91    inference(subsumption_resolution,[],[f2905,f73])).
% 3.92/0.91  fof(f73,plain,(
% 3.92/0.91    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 3.92/0.91    inference(cnf_transformation,[],[f44])).
% 3.92/0.91  fof(f44,plain,(
% 3.92/0.91    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f43,f42])).
% 3.92/0.91  fof(f42,plain,(
% 3.92/0.91    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f43,plain,(
% 3.92/0.91    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f27,plain,(
% 3.92/0.91    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.92/0.91    inference(flattening,[],[f26])).
% 3.92/0.91  fof(f26,plain,(
% 3.92/0.91    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.92/0.91    inference(ennf_transformation,[],[f23])).
% 3.92/0.91  fof(f23,negated_conjecture,(
% 3.92/0.91    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.92/0.91    inference(negated_conjecture,[],[f22])).
% 3.92/0.91  fof(f22,conjecture,(
% 3.92/0.91    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 3.92/0.91  fof(f2905,plain,(
% 3.92/0.91    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.92/0.91    inference(resolution,[],[f479,f1141])).
% 3.92/0.91  fof(f1141,plain,(
% 3.92/0.91    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 3.92/0.91    inference(resolution,[],[f1124,f598])).
% 3.92/0.91  fof(f598,plain,(
% 3.92/0.91    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK1)) | r1_tarski(X2,k3_relat_1(sK1))) )),
% 3.92/0.91    inference(superposition,[],[f117,f328])).
% 3.92/0.91  fof(f328,plain,(
% 3.92/0.91    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 3.92/0.91    inference(resolution,[],[f113,f71])).
% 3.92/0.91  fof(f71,plain,(
% 3.92/0.91    v1_relat_1(sK1)),
% 3.92/0.91    inference(cnf_transformation,[],[f44])).
% 3.92/0.91  fof(f113,plain,(
% 3.92/0.91    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 3.92/0.91    inference(definition_unfolding,[],[f76,f112])).
% 3.92/0.91  fof(f112,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.92/0.91    inference(definition_unfolding,[],[f86,f87])).
% 3.92/0.91  fof(f87,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f12])).
% 3.92/0.91  fof(f12,axiom,(
% 3.92/0.91    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.92/0.91  fof(f86,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.92/0.91    inference(cnf_transformation,[],[f13])).
% 3.92/0.91  fof(f13,axiom,(
% 3.92/0.91    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.92/0.91  fof(f76,plain,(
% 3.92/0.91    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f28])).
% 3.92/0.91  fof(f28,plain,(
% 3.92/0.91    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.92/0.91    inference(ennf_transformation,[],[f19])).
% 3.92/0.91  fof(f19,axiom,(
% 3.92/0.91    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 3.92/0.91  fof(f117,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f106,f112])).
% 3.92/0.91  fof(f106,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f36])).
% 3.92/0.91  fof(f36,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.92/0.91    inference(ennf_transformation,[],[f5])).
% 3.92/0.91  fof(f5,axiom,(
% 3.92/0.91    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.92/0.91  fof(f1124,plain,(
% 3.92/0.91    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 3.92/0.91    inference(resolution,[],[f950,f163])).
% 3.92/0.91  fof(f163,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(subsumption_resolution,[],[f157,f75])).
% 3.92/0.91  fof(f75,plain,(
% 3.92/0.91    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f7])).
% 3.92/0.91  fof(f7,axiom,(
% 3.92/0.91    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.92/0.91  fof(f157,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(extensionality_resolution,[],[f93,f116])).
% 3.92/0.91  fof(f116,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f102,f85])).
% 3.92/0.91  fof(f85,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f16])).
% 3.92/0.91  fof(f16,axiom,(
% 3.92/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.92/0.91  fof(f102,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f65])).
% 3.92/0.91  fof(f65,plain,(
% 3.92/0.91    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.92/0.91    inference(nnf_transformation,[],[f4])).
% 3.92/0.91  fof(f4,axiom,(
% 3.92/0.91    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.92/0.91  fof(f93,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f52])).
% 3.92/0.91  fof(f52,plain,(
% 3.92/0.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/0.91    inference(flattening,[],[f51])).
% 3.92/0.91  fof(f51,plain,(
% 3.92/0.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/0.91    inference(nnf_transformation,[],[f3])).
% 3.92/0.91  fof(f3,axiom,(
% 3.92/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.92/0.91  fof(f950,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 3.92/0.91    inference(backward_demodulation,[],[f369,f888])).
% 3.92/0.91  fof(f888,plain,(
% 3.92/0.91    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.92/0.91    inference(resolution,[],[f864,f281])).
% 3.92/0.91  fof(f281,plain,(
% 3.92/0.91    ( ! [X6] : (r2_hidden(sK11(X6),X6) | k1_xboole_0 = k2_relat_1(X6)) )),
% 3.92/0.91    inference(resolution,[],[f274,f79])).
% 3.92/0.91  fof(f79,plain,(
% 3.92/0.91    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.92/0.91    inference(cnf_transformation,[],[f46])).
% 3.92/0.91  fof(f46,plain,(
% 3.92/0.91    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f45])).
% 3.92/0.91  fof(f45,plain,(
% 3.92/0.91    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f31,plain,(
% 3.92/0.91    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.92/0.91    inference(ennf_transformation,[],[f2])).
% 3.92/0.91  fof(f2,axiom,(
% 3.92/0.91    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.92/0.91  fof(f274,plain,(
% 3.92/0.91    ( ! [X8,X7] : (~r2_hidden(X7,k2_relat_1(X8)) | r2_hidden(sK11(X8),X8)) )),
% 3.92/0.91    inference(resolution,[],[f128,f104])).
% 3.92/0.91  fof(f104,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK11(X1),X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f67])).
% 3.92/0.91  fof(f67,plain,(
% 3.92/0.91    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK11(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK11(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f35,f66])).
% 3.92/0.91  fof(f66,plain,(
% 3.92/0.91    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK11(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK11(X1),X1)))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f35,plain,(
% 3.92/0.91    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.92/0.91    inference(ennf_transformation,[],[f15])).
% 3.92/0.91  fof(f15,axiom,(
% 3.92/0.91    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 3.92/0.91  fof(f128,plain,(
% 3.92/0.91    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.92/0.91    inference(equality_resolution,[],[f98])).
% 3.92/0.91  fof(f98,plain,(
% 3.92/0.91    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.92/0.91    inference(cnf_transformation,[],[f64])).
% 3.92/0.91  fof(f64,plain,(
% 3.92/0.91    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f60,f63,f62,f61])).
% 3.92/0.91  fof(f61,plain,(
% 3.92/0.91    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f62,plain,(
% 3.92/0.91    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0) => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f63,plain,(
% 3.92/0.91    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f60,plain,(
% 3.92/0.91    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.92/0.91    inference(rectify,[],[f59])).
% 3.92/0.91  fof(f59,plain,(
% 3.92/0.91    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.92/0.91    inference(nnf_transformation,[],[f18])).
% 3.92/0.91  fof(f18,axiom,(
% 3.92/0.91    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 3.92/0.91  fof(f864,plain,(
% 3.92/0.91    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.92/0.91    inference(resolution,[],[f859,f148])).
% 3.92/0.91  fof(f148,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_xboole_0(X0,sK3(X1)) | ~r2_hidden(X1,X0)) )),
% 3.92/0.91    inference(resolution,[],[f90,f80])).
% 3.92/0.91  fof(f80,plain,(
% 3.92/0.91    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 3.92/0.91    inference(cnf_transformation,[],[f48])).
% 3.92/0.91  fof(f48,plain,(
% 3.92/0.91    ! [X0] : (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),sK3(X0)) | ~r2_hidden(X3,sK3(X0))) & ! [X4,X5] : (r2_hidden(X5,sK3(X0)) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f47])).
% 3.92/0.91  fof(f47,plain,(
% 3.92/0.91    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),sK3(X0)) | ~r2_hidden(X3,sK3(X0))) & ! [X5,X4] : (r2_hidden(X5,sK3(X0)) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f33,plain,(
% 3.92/0.91    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1))),
% 3.92/0.91    inference(flattening,[],[f32])).
% 3.92/0.91  fof(f32,plain,(
% 3.92/0.91    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | (~r1_tarski(X5,X4) | ~r2_hidden(X4,X1))) & r2_hidden(X0,X1))),
% 3.92/0.91    inference(ennf_transformation,[],[f24])).
% 3.92/0.91  fof(f24,plain,(
% 3.92/0.91    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 3.92/0.91    inference(rectify,[],[f14])).
% 3.92/0.91  fof(f14,axiom,(
% 3.92/0.91    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k1_zfmisc_1(X2),X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).
% 3.92/0.91  fof(f90,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f50])).
% 3.92/0.91  fof(f50,plain,(
% 3.92/0.91    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f49])).
% 3.92/0.91  fof(f49,plain,(
% 3.92/0.91    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f34,plain,(
% 3.92/0.91    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.92/0.91    inference(ennf_transformation,[],[f25])).
% 3.92/0.91  fof(f25,plain,(
% 3.92/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.92/0.91    inference(rectify,[],[f1])).
% 3.92/0.91  fof(f1,axiom,(
% 3.92/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.92/0.91  fof(f859,plain,(
% 3.92/0.91    ( ! [X4] : (r1_xboole_0(k1_xboole_0,X4)) )),
% 3.92/0.91    inference(resolution,[],[f855,f74])).
% 3.92/0.91  fof(f74,plain,(
% 3.92/0.91    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f9])).
% 3.92/0.91  fof(f9,axiom,(
% 3.92/0.91    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.92/0.91  fof(f855,plain,(
% 3.92/0.91    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 3.92/0.91    inference(duplicate_literal_removal,[],[f850])).
% 3.92/0.91  fof(f850,plain,(
% 3.92/0.91    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 3.92/0.91    inference(resolution,[],[f151,f89])).
% 3.92/0.91  fof(f89,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f50])).
% 3.92/0.91  fof(f151,plain,(
% 3.92/0.91    ( ! [X8,X7,X9] : (~r2_hidden(sK4(X8,X9),X7) | ~r1_xboole_0(X7,X8) | r1_xboole_0(X8,X9)) )),
% 3.92/0.91    inference(resolution,[],[f90,f88])).
% 3.92/0.91  fof(f88,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f50])).
% 3.92/0.91  fof(f369,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 3.92/0.91    inference(subsumption_resolution,[],[f368,f70])).
% 3.92/0.91  fof(f70,plain,(
% 3.92/0.91    v1_relat_1(sK0)),
% 3.92/0.91    inference(cnf_transformation,[],[f44])).
% 3.92/0.91  fof(f368,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 3.92/0.91    inference(subsumption_resolution,[],[f362,f71])).
% 3.92/0.91  fof(f362,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.92/0.91    inference(superposition,[],[f77,f136])).
% 3.92/0.91  fof(f136,plain,(
% 3.92/0.91    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 3.92/0.91    inference(resolution,[],[f115,f72])).
% 3.92/0.91  fof(f72,plain,(
% 3.92/0.91    r1_tarski(sK0,sK1)),
% 3.92/0.91    inference(cnf_transformation,[],[f44])).
% 3.92/0.91  fof(f115,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f103,f85])).
% 3.92/0.91  fof(f103,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f65])).
% 3.92/0.91  fof(f77,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f29])).
% 3.92/0.91  fof(f29,plain,(
% 3.92/0.91    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.92/0.91    inference(ennf_transformation,[],[f21])).
% 3.92/0.91  fof(f21,axiom,(
% 3.92/0.91    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 3.92/0.91  fof(f479,plain,(
% 3.92/0.91    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 3.92/0.91    inference(superposition,[],[f119,f327])).
% 3.92/0.91  fof(f327,plain,(
% 3.92/0.91    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 3.92/0.91    inference(resolution,[],[f113,f70])).
% 3.92/0.91  fof(f119,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f108,f112])).
% 3.92/0.91  fof(f108,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f39])).
% 3.92/0.91  fof(f39,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.92/0.91    inference(flattening,[],[f38])).
% 3.92/0.91  fof(f38,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.92/0.91    inference(ennf_transformation,[],[f11])).
% 3.92/0.91  fof(f11,axiom,(
% 3.92/0.91    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.92/0.91  fof(f5594,plain,(
% 3.92/0.91    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.92/0.91    inference(resolution,[],[f5522,f1093])).
% 3.92/0.91  fof(f1093,plain,(
% 3.92/0.91    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 3.92/0.91    inference(resolution,[],[f933,f163])).
% 3.92/0.91  fof(f933,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 3.92/0.91    inference(backward_demodulation,[],[f400,f885])).
% 3.92/0.91  fof(f885,plain,(
% 3.92/0.91    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.92/0.91    inference(resolution,[],[f864,f250])).
% 3.92/0.91  fof(f250,plain,(
% 3.92/0.91    ( ! [X4] : (r2_hidden(sK11(X4),X4) | k1_xboole_0 = k1_relat_1(X4)) )),
% 3.92/0.91    inference(resolution,[],[f245,f79])).
% 3.92/0.91  fof(f245,plain,(
% 3.92/0.91    ( ! [X8,X7] : (~r2_hidden(X7,k1_relat_1(X8)) | r2_hidden(sK11(X8),X8)) )),
% 3.92/0.91    inference(resolution,[],[f126,f104])).
% 3.92/0.91  fof(f126,plain,(
% 3.92/0.91    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.92/0.91    inference(equality_resolution,[],[f94])).
% 3.92/0.91  fof(f94,plain,(
% 3.92/0.91    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.92/0.91    inference(cnf_transformation,[],[f58])).
% 3.92/0.91  fof(f58,plain,(
% 3.92/0.91    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f54,f57,f56,f55])).
% 3.92/0.91  fof(f55,plain,(
% 3.92/0.91    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f56,plain,(
% 3.92/0.91    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f57,plain,(
% 3.92/0.91    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f54,plain,(
% 3.92/0.91    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.92/0.91    inference(rectify,[],[f53])).
% 3.92/0.91  fof(f53,plain,(
% 3.92/0.91    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.92/0.91    inference(nnf_transformation,[],[f17])).
% 3.92/0.91  fof(f17,axiom,(
% 3.92/0.91    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 3.92/0.91  fof(f400,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 3.92/0.91    inference(subsumption_resolution,[],[f399,f70])).
% 3.92/0.91  fof(f399,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 3.92/0.91    inference(subsumption_resolution,[],[f393,f71])).
% 3.92/0.91  fof(f393,plain,(
% 3.92/0.91    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.92/0.91    inference(superposition,[],[f78,f136])).
% 3.92/0.91  fof(f78,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f30])).
% 3.92/0.91  fof(f30,plain,(
% 3.92/0.91    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.92/0.91    inference(ennf_transformation,[],[f20])).
% 3.92/0.91  fof(f20,axiom,(
% 3.92/0.91    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 3.92/0.91  fof(f5522,plain,(
% 3.92/0.91    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 3.92/0.91    inference(superposition,[],[f117,f808])).
% 3.92/0.91  fof(f808,plain,(
% 3.92/0.91    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k1_relat_1(sK1)))),
% 3.92/0.91    inference(resolution,[],[f616,f600])).
% 3.92/0.91  fof(f600,plain,(
% 3.92/0.91    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 3.92/0.91    inference(superposition,[],[f114,f328])).
% 3.92/0.91  fof(f114,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.92/0.91    inference(definition_unfolding,[],[f84,f112])).
% 3.92/0.91  fof(f84,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.92/0.91    inference(cnf_transformation,[],[f10])).
% 3.92/0.91  fof(f10,axiom,(
% 3.92/0.91    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.92/0.91  fof(f616,plain,(
% 3.92/0.91    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0) )),
% 3.92/0.91    inference(subsumption_resolution,[],[f615,f123])).
% 3.92/0.91  fof(f123,plain,(
% 3.92/0.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.92/0.91    inference(equality_resolution,[],[f92])).
% 3.92/0.91  fof(f92,plain,(
% 3.92/0.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.92/0.91    inference(cnf_transformation,[],[f52])).
% 3.92/0.91  fof(f615,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 3.92/0.91    inference(duplicate_literal_removal,[],[f612])).
% 3.92/0.91  fof(f612,plain,(
% 3.92/0.91    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 3.92/0.91    inference(resolution,[],[f122,f120])).
% 3.92/0.91  fof(f120,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK12(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f111,f112])).
% 3.92/0.91  fof(f111,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK12(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f69])).
% 3.92/0.91  fof(f69,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK12(X0,X1,X2)) & r1_tarski(X2,sK12(X0,X1,X2)) & r1_tarski(X0,sK12(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.92/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f41,f68])).
% 3.92/0.91  fof(f68,plain,(
% 3.92/0.91    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK12(X0,X1,X2)) & r1_tarski(X2,sK12(X0,X1,X2)) & r1_tarski(X0,sK12(X0,X1,X2))))),
% 3.92/0.91    introduced(choice_axiom,[])).
% 3.92/0.91  fof(f41,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.92/0.91    inference(flattening,[],[f40])).
% 3.92/0.91  fof(f40,plain,(
% 3.92/0.91    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.92/0.91    inference(ennf_transformation,[],[f6])).
% 3.92/0.91  fof(f6,axiom,(
% 3.92/0.91    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 3.92/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 3.92/0.91  fof(f122,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,sK12(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(definition_unfolding,[],[f109,f112])).
% 3.92/0.91  fof(f109,plain,(
% 3.92/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK12(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.92/0.91    inference(cnf_transformation,[],[f69])).
% 3.92/0.91  % SZS output end Proof for theBenchmark
% 3.92/0.92  % (12816)------------------------------
% 3.92/0.92  % (12816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.92  % (12816)Termination reason: Refutation
% 3.92/0.92  
% 3.92/0.92  % (12816)Memory used [KB]: 15863
% 3.92/0.92  % (12816)Time elapsed: 0.418 s
% 3.92/0.92  % (12816)------------------------------
% 3.92/0.92  % (12816)------------------------------
% 3.92/0.92  % (12809)Success in time 0.557 s
%------------------------------------------------------------------------------
