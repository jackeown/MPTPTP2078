%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:14 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 296 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  417 ( 862 expanded)
%              Number of equality atoms :   50 ( 130 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2077,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2076,f64])).

fof(f64,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f2076,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2075,f66])).

fof(f66,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f2075,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2074,f723])).

fof(f723,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f687,f421])).

fof(f421,plain,(
    ! [X3] :
      ( ~ r1_tarski(k6_subset_1(X3,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X3,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f110,f315])).

fof(f315,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f103,f65])).

fof(f65,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f83,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f69,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f98,f102,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f687,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),X0) ),
    inference(resolution,[],[f647,f145])).

fof(f145,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f99,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f647,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f646,f209])).

fof(f209,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f206,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f116,f149])).

fof(f149,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(resolution,[],[f143,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,sK3(X1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f86,f74])).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK3(X0))
          | r2_tarski(X2,sK3(X0))
          | ~ r1_tarski(X2,sK3(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK4(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK4(X0,X3),sK3(X0)) )
          | ~ r2_hidden(X3,sK3(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK3(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK3(X0))
            | r2_tarski(X2,sK3(X0))
            | ~ r1_tarski(X2,sK3(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK3(X0)) )
            | ~ r2_hidden(X3,sK3(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK3(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,sK3(X0)) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK4(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK4(X0,X3),sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
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
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f143,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f106,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f124,f105])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f124,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f89,f68])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f106,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f91,f81])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f116,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f646,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f645,f64])).

fof(f645,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f625,f65])).

fof(f625,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f70,f593])).

fof(f593,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f585,f124])).

fof(f585,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,sK1),X0) ),
    inference(resolution,[],[f548,f523])).

fof(f523,plain,(
    ! [X37,X36] : r1_xboole_0(k6_subset_1(X36,X37),X37) ),
    inference(trivial_inequality_removal,[],[f513])).

fof(f513,plain,(
    ! [X37,X36] :
      ( k6_subset_1(X36,X37) != k6_subset_1(X36,X37)
      | r1_xboole_0(k6_subset_1(X36,X37),X37) ) ),
    inference(superposition,[],[f106,f336])).

fof(f336,plain,(
    ! [X0,X1] : k6_subset_1(X1,X0) = k6_subset_1(k6_subset_1(X1,X0),X0) ),
    inference(superposition,[],[f108,f104])).

fof(f104,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f79,f102])).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f108,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f96,f81,f81,f81,f102])).

fof(f96,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f548,plain,(
    ! [X41,X42] :
      ( ~ r1_xboole_0(k6_subset_1(sK0,X41),sK1)
      | r1_tarski(k6_subset_1(sK0,X41),X42) ) ),
    inference(resolution,[],[f409,f157])).

fof(f157,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),sK1) ),
    inference(resolution,[],[f147,f105])).

fof(f147,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,sK0)
      | r1_tarski(X7,sK1) ) ),
    inference(resolution,[],[f99,f66])).

fof(f409,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_tarski(X3,X5)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f112,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f97,f102])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f101,f102])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f70,plain,(
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

fof(f2074,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2065,f67])).

fof(f67,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f2065,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f396,f430])).

fof(f430,plain,(
    ! [X8] :
      ( r1_tarski(k2_relat_1(X8),k3_relat_1(sK1))
      | ~ r1_tarski(X8,sK1)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f429,f65])).

fof(f429,plain,(
    ! [X8] :
      ( r1_tarski(k2_relat_1(X8),k3_relat_1(sK1))
      | ~ r1_tarski(X8,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f422,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f422,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k2_relat_1(sK1))
      | r1_tarski(X4,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f109,f315])).

fof(f396,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(sK0),X2)
      | r1_tarski(k3_relat_1(sK0),X2)
      | ~ r1_tarski(k1_relat_1(sK0),X2) ) ),
    inference(superposition,[],[f111,f314])).

fof(f314,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f103,f64])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f100,f102])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:07:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.45  % (10616)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.47  % (10624)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.53  % (10619)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.56/0.55  % (10631)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.55  % (10611)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.55  % (10609)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.55  % (10612)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.55  % (10614)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.56  % (10636)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.56  % (10617)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.56  % (10632)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.56  % (10622)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.56  % (10633)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.56  % (10623)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.56  % (10628)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.57  % (10630)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.56/0.57  % (10625)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.57  % (10620)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.57  % (10615)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.57  % (10638)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.57  % (10613)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.58  % (10635)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.59  % (10627)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.59  % (10610)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.60  % (10618)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.61  % (10637)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.61  % (10634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.61  % (10629)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.62  % (10626)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.62  % (10621)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 3.12/0.76  % (10612)Refutation not found, incomplete strategy% (10612)------------------------------
% 3.12/0.76  % (10612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.76  % (10612)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.76  
% 3.12/0.76  % (10612)Memory used [KB]: 6140
% 3.12/0.76  % (10612)Time elapsed: 0.326 s
% 3.12/0.76  % (10612)------------------------------
% 3.12/0.76  % (10612)------------------------------
% 3.24/0.77  % (10615)Refutation found. Thanks to Tanya!
% 3.24/0.77  % SZS status Theorem for theBenchmark
% 3.24/0.78  % SZS output start Proof for theBenchmark
% 3.24/0.78  fof(f2077,plain,(
% 3.24/0.78    $false),
% 3.24/0.78    inference(subsumption_resolution,[],[f2076,f64])).
% 3.24/0.78  fof(f64,plain,(
% 3.24/0.78    v1_relat_1(sK0)),
% 3.24/0.78    inference(cnf_transformation,[],[f47])).
% 3.24/0.78  fof(f47,plain,(
% 3.24/0.78    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f46,f45])).
% 3.24/0.78  fof(f45,plain,(
% 3.24/0.78    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f46,plain,(
% 3.24/0.78    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f28,plain,(
% 3.24/0.78    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.24/0.78    inference(flattening,[],[f27])).
% 3.24/0.78  fof(f27,plain,(
% 3.24/0.78    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.24/0.78    inference(ennf_transformation,[],[f23])).
% 3.24/0.78  fof(f23,negated_conjecture,(
% 3.24/0.78    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.24/0.78    inference(negated_conjecture,[],[f22])).
% 3.24/0.78  fof(f22,conjecture,(
% 3.24/0.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 3.24/0.78  fof(f2076,plain,(
% 3.24/0.78    ~v1_relat_1(sK0)),
% 3.24/0.78    inference(subsumption_resolution,[],[f2075,f66])).
% 3.24/0.78  fof(f66,plain,(
% 3.24/0.78    r1_tarski(sK0,sK1)),
% 3.24/0.78    inference(cnf_transformation,[],[f47])).
% 3.24/0.78  fof(f2075,plain,(
% 3.24/0.78    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 3.24/0.78    inference(subsumption_resolution,[],[f2074,f723])).
% 3.24/0.78  fof(f723,plain,(
% 3.24/0.78    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.24/0.78    inference(resolution,[],[f687,f421])).
% 3.24/0.78  fof(f421,plain,(
% 3.24/0.78    ( ! [X3] : (~r1_tarski(k6_subset_1(X3,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X3,k3_relat_1(sK1))) )),
% 3.24/0.78    inference(superposition,[],[f110,f315])).
% 3.24/0.78  fof(f315,plain,(
% 3.24/0.78    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 3.24/0.78    inference(resolution,[],[f103,f65])).
% 3.24/0.78  fof(f65,plain,(
% 3.24/0.78    v1_relat_1(sK1)),
% 3.24/0.78    inference(cnf_transformation,[],[f47])).
% 3.24/0.78  fof(f103,plain,(
% 3.24/0.78    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f69,f102])).
% 3.24/0.78  fof(f102,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f82,f83])).
% 3.24/0.78  fof(f83,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f14])).
% 3.24/0.78  fof(f14,axiom,(
% 3.24/0.78    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.24/0.78  fof(f82,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f15])).
% 3.24/0.78  fof(f15,axiom,(
% 3.24/0.78    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.24/0.78  fof(f69,plain,(
% 3.24/0.78    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f29])).
% 3.24/0.78  fof(f29,plain,(
% 3.24/0.78    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.24/0.78    inference(ennf_transformation,[],[f19])).
% 3.24/0.78  fof(f19,axiom,(
% 3.24/0.78    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 3.24/0.78  fof(f110,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f98,f102,f81])).
% 3.24/0.78  fof(f81,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f17])).
% 3.24/0.78  fof(f17,axiom,(
% 3.24/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.24/0.78  fof(f98,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f38])).
% 3.24/0.78  fof(f38,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.24/0.78    inference(ennf_transformation,[],[f10])).
% 3.24/0.78  fof(f10,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.24/0.78  fof(f687,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),X0)) )),
% 3.24/0.78    inference(resolution,[],[f647,f145])).
% 3.24/0.78  fof(f145,plain,(
% 3.24/0.78    ( ! [X2,X3] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X3)) )),
% 3.24/0.78    inference(resolution,[],[f99,f68])).
% 3.24/0.78  fof(f68,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f7])).
% 3.24/0.78  fof(f7,axiom,(
% 3.24/0.78    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.24/0.78  fof(f99,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f40])).
% 3.24/0.78  fof(f40,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.24/0.78    inference(flattening,[],[f39])).
% 3.24/0.78  fof(f39,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.24/0.78    inference(ennf_transformation,[],[f6])).
% 3.24/0.78  fof(f6,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.24/0.78  fof(f647,plain,(
% 3.24/0.78    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 3.24/0.78    inference(forward_demodulation,[],[f646,f209])).
% 3.24/0.78  fof(f209,plain,(
% 3.24/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.24/0.78    inference(resolution,[],[f206,f73])).
% 3.24/0.78  fof(f73,plain,(
% 3.24/0.78    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f49])).
% 3.24/0.78  fof(f49,plain,(
% 3.24/0.78    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f48])).
% 3.24/0.78  fof(f48,plain,(
% 3.24/0.78    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f33,plain,(
% 3.24/0.78    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.24/0.78    inference(ennf_transformation,[],[f3])).
% 3.24/0.78  fof(f3,axiom,(
% 3.24/0.78    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.24/0.78  fof(f206,plain,(
% 3.24/0.78    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(k1_xboole_0))) )),
% 3.24/0.78    inference(resolution,[],[f116,f149])).
% 3.24/0.78  fof(f149,plain,(
% 3.24/0.78    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 3.24/0.78    inference(resolution,[],[f143,f117])).
% 3.24/0.78  fof(f117,plain,(
% 3.24/0.78    ( ! [X0,X1] : (~r1_xboole_0(X0,sK3(X1)) | ~r2_hidden(X1,X0)) )),
% 3.24/0.78    inference(resolution,[],[f86,f74])).
% 3.24/0.78  fof(f74,plain,(
% 3.24/0.78    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f52])).
% 3.24/0.78  fof(f52,plain,(
% 3.24/0.78    ! [X0] : (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : ((! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X6,X7] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f51,f50])).
% 3.24/0.78  fof(f50,plain,(
% 3.24/0.78    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X7,X6] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f51,plain,(
% 3.24/0.78    ! [X3,X0] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) => (! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f35,plain,(
% 3.24/0.78    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 3.24/0.78    inference(flattening,[],[f34])).
% 3.24/0.78  fof(f34,plain,(
% 3.24/0.78    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 3.24/0.78    inference(ennf_transformation,[],[f24])).
% 3.24/0.78  fof(f24,plain,(
% 3.24/0.78    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 3.24/0.78    inference(rectify,[],[f16])).
% 3.24/0.78  fof(f16,axiom,(
% 3.24/0.78    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).
% 3.24/0.78  fof(f86,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f54])).
% 3.24/0.78  fof(f54,plain,(
% 3.24/0.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f53])).
% 3.24/0.78  fof(f53,plain,(
% 3.24/0.78    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f36,plain,(
% 3.24/0.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.24/0.78    inference(ennf_transformation,[],[f26])).
% 3.24/0.78  fof(f26,plain,(
% 3.24/0.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.24/0.78    inference(rectify,[],[f2])).
% 3.24/0.78  fof(f2,axiom,(
% 3.24/0.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.24/0.78  fof(f143,plain,(
% 3.24/0.78    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 3.24/0.78    inference(trivial_inequality_removal,[],[f141])).
% 3.24/0.78  fof(f141,plain,(
% 3.24/0.78    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 3.24/0.78    inference(superposition,[],[f106,f140])).
% 3.24/0.78  fof(f140,plain,(
% 3.24/0.78    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 3.24/0.78    inference(resolution,[],[f124,f105])).
% 3.24/0.78  fof(f105,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f80,f81])).
% 3.24/0.78  fof(f80,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f8])).
% 3.24/0.78  fof(f8,axiom,(
% 3.24/0.78    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.24/0.78  fof(f124,plain,(
% 3.24/0.78    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 3.24/0.78    inference(resolution,[],[f89,f68])).
% 3.24/0.78  fof(f89,plain,(
% 3.24/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f56])).
% 3.24/0.78  fof(f56,plain,(
% 3.24/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.24/0.78    inference(flattening,[],[f55])).
% 3.24/0.78  fof(f55,plain,(
% 3.24/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.24/0.78    inference(nnf_transformation,[],[f4])).
% 3.24/0.78  fof(f4,axiom,(
% 3.24/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.24/0.78  fof(f106,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f91,f81])).
% 3.24/0.78  fof(f91,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f57])).
% 3.24/0.78  fof(f57,plain,(
% 3.24/0.78    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.24/0.78    inference(nnf_transformation,[],[f12])).
% 3.24/0.78  fof(f12,axiom,(
% 3.24/0.78    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.24/0.78  fof(f116,plain,(
% 3.24/0.78    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.24/0.78    inference(equality_resolution,[],[f92])).
% 3.24/0.78  fof(f92,plain,(
% 3.24/0.78    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.24/0.78    inference(cnf_transformation,[],[f63])).
% 3.24/0.78  fof(f63,plain,(
% 3.24/0.78    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f59,f62,f61,f60])).
% 3.24/0.78  fof(f60,plain,(
% 3.24/0.78    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f61,plain,(
% 3.24/0.78    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f62,plain,(
% 3.24/0.78    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f59,plain,(
% 3.24/0.78    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.24/0.78    inference(rectify,[],[f58])).
% 3.24/0.78  fof(f58,plain,(
% 3.24/0.78    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.24/0.78    inference(nnf_transformation,[],[f18])).
% 3.24/0.78  fof(f18,axiom,(
% 3.24/0.78    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 3.24/0.78  fof(f646,plain,(
% 3.24/0.78    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 3.24/0.78    inference(subsumption_resolution,[],[f645,f64])).
% 3.24/0.78  fof(f645,plain,(
% 3.24/0.78    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 3.24/0.78    inference(subsumption_resolution,[],[f625,f65])).
% 3.24/0.78  fof(f625,plain,(
% 3.24/0.78    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.24/0.78    inference(superposition,[],[f70,f593])).
% 3.24/0.78  fof(f593,plain,(
% 3.24/0.78    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 3.24/0.78    inference(resolution,[],[f585,f124])).
% 3.24/0.78  fof(f585,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,sK1),X0)) )),
% 3.24/0.78    inference(resolution,[],[f548,f523])).
% 3.24/0.78  fof(f523,plain,(
% 3.24/0.78    ( ! [X37,X36] : (r1_xboole_0(k6_subset_1(X36,X37),X37)) )),
% 3.24/0.78    inference(trivial_inequality_removal,[],[f513])).
% 3.24/0.78  fof(f513,plain,(
% 3.24/0.78    ( ! [X37,X36] : (k6_subset_1(X36,X37) != k6_subset_1(X36,X37) | r1_xboole_0(k6_subset_1(X36,X37),X37)) )),
% 3.24/0.78    inference(superposition,[],[f106,f336])).
% 3.24/0.78  fof(f336,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k6_subset_1(X1,X0) = k6_subset_1(k6_subset_1(X1,X0),X0)) )),
% 3.24/0.78    inference(superposition,[],[f108,f104])).
% 3.24/0.78  fof(f104,plain,(
% 3.24/0.78    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 3.24/0.78    inference(definition_unfolding,[],[f79,f102])).
% 3.24/0.78  fof(f79,plain,(
% 3.24/0.78    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f25])).
% 3.24/0.78  fof(f25,plain,(
% 3.24/0.78    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.24/0.78    inference(rectify,[],[f1])).
% 3.24/0.78  fof(f1,axiom,(
% 3.24/0.78    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.24/0.78  fof(f108,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f96,f81,f81,f81,f102])).
% 3.24/0.78  fof(f96,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f9])).
% 3.24/0.78  fof(f9,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.24/0.78  fof(f548,plain,(
% 3.24/0.78    ( ! [X41,X42] : (~r1_xboole_0(k6_subset_1(sK0,X41),sK1) | r1_tarski(k6_subset_1(sK0,X41),X42)) )),
% 3.24/0.78    inference(resolution,[],[f409,f157])).
% 3.24/0.78  fof(f157,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),sK1)) )),
% 3.24/0.78    inference(resolution,[],[f147,f105])).
% 3.24/0.78  fof(f147,plain,(
% 3.24/0.78    ( ! [X7] : (~r1_tarski(X7,sK0) | r1_tarski(X7,sK1)) )),
% 3.24/0.78    inference(resolution,[],[f99,f66])).
% 3.24/0.78  fof(f409,plain,(
% 3.24/0.78    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r1_tarski(X3,X5) | ~r1_xboole_0(X3,X4)) )),
% 3.24/0.78    inference(resolution,[],[f112,f109])).
% 3.24/0.78  fof(f109,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f97,f102])).
% 3.24/0.78  fof(f97,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f37])).
% 3.24/0.78  fof(f37,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.24/0.78    inference(ennf_transformation,[],[f5])).
% 3.24/0.78  fof(f5,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.24/0.78  fof(f112,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f101,f102])).
% 3.24/0.78  fof(f101,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f44])).
% 3.24/0.78  fof(f44,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.24/0.78    inference(flattening,[],[f43])).
% 3.24/0.78  fof(f43,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.24/0.78    inference(ennf_transformation,[],[f11])).
% 3.24/0.78  fof(f11,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 3.24/0.78  fof(f70,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f30])).
% 3.24/0.78  fof(f30,plain,(
% 3.24/0.78    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.24/0.78    inference(ennf_transformation,[],[f20])).
% 3.24/0.78  fof(f20,axiom,(
% 3.24/0.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 3.24/0.78  fof(f2074,plain,(
% 3.24/0.78    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 3.24/0.78    inference(subsumption_resolution,[],[f2065,f67])).
% 3.24/0.78  fof(f67,plain,(
% 3.24/0.78    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 3.24/0.78    inference(cnf_transformation,[],[f47])).
% 3.24/0.78  fof(f2065,plain,(
% 3.24/0.78    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 3.24/0.78    inference(resolution,[],[f396,f430])).
% 3.24/0.78  fof(f430,plain,(
% 3.24/0.78    ( ! [X8] : (r1_tarski(k2_relat_1(X8),k3_relat_1(sK1)) | ~r1_tarski(X8,sK1) | ~v1_relat_1(X8)) )),
% 3.24/0.78    inference(subsumption_resolution,[],[f429,f65])).
% 3.24/0.78  fof(f429,plain,(
% 3.24/0.78    ( ! [X8] : (r1_tarski(k2_relat_1(X8),k3_relat_1(sK1)) | ~r1_tarski(X8,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X8)) )),
% 3.24/0.78    inference(resolution,[],[f422,f72])).
% 3.24/0.78  fof(f72,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f32])).
% 3.24/0.78  fof(f32,plain,(
% 3.24/0.78    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.24/0.78    inference(flattening,[],[f31])).
% 3.24/0.78  fof(f31,plain,(
% 3.24/0.78    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.24/0.78    inference(ennf_transformation,[],[f21])).
% 3.24/0.78  fof(f21,axiom,(
% 3.24/0.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 3.24/0.78  fof(f422,plain,(
% 3.24/0.78    ( ! [X4] : (~r1_tarski(X4,k2_relat_1(sK1)) | r1_tarski(X4,k3_relat_1(sK1))) )),
% 3.24/0.78    inference(superposition,[],[f109,f315])).
% 3.24/0.78  fof(f396,plain,(
% 3.24/0.78    ( ! [X2] : (~r1_tarski(k2_relat_1(sK0),X2) | r1_tarski(k3_relat_1(sK0),X2) | ~r1_tarski(k1_relat_1(sK0),X2)) )),
% 3.24/0.78    inference(superposition,[],[f111,f314])).
% 3.24/0.78  fof(f314,plain,(
% 3.24/0.78    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 3.24/0.78    inference(resolution,[],[f103,f64])).
% 3.24/0.78  fof(f111,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f100,f102])).
% 3.24/0.78  fof(f100,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f42])).
% 3.24/0.78  fof(f42,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.24/0.78    inference(flattening,[],[f41])).
% 3.24/0.78  fof(f41,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.24/0.78    inference(ennf_transformation,[],[f13])).
% 3.24/0.78  fof(f13,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.24/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.24/0.78  % SZS output end Proof for theBenchmark
% 3.24/0.78  % (10615)------------------------------
% 3.24/0.78  % (10615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.78  % (10615)Termination reason: Refutation
% 3.24/0.78  
% 3.24/0.78  % (10615)Memory used [KB]: 12409
% 3.24/0.78  % (10615)Time elapsed: 0.280 s
% 3.24/0.78  % (10615)------------------------------
% 3.24/0.78  % (10615)------------------------------
% 3.24/0.79  % (10608)Success in time 0.442 s
%------------------------------------------------------------------------------
