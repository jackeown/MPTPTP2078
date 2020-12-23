%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 605 expanded)
%              Number of leaves         :   38 ( 187 expanded)
%              Depth                    :   18
%              Number of atoms          :  538 (1760 expanded)
%              Number of equality atoms :   75 ( 386 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1602,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1551,f1569,f310])).

fof(f310,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_relat_1(sK1))
      | ~ r1_tarski(X2,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f170,f231])).

fof(f231,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f119,f74])).

fof(f74,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f46,f45])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f80,f117])).

fof(f117,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f93,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f80,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f122,f121])).

fof(f121,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f90,f92,f92])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f110,f117])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1569,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f1553,f738])).

fof(f738,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f725,f311])).

fof(f311,plain,(
    ! [X3] :
      ( r1_tarski(X3,k3_relat_1(sK1))
      | ~ r1_tarski(X3,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f122,f231])).

fof(f725,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f271,f76])).

fof(f76,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f271,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f125,f230])).

fof(f230,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f119,f73])).

fof(f73,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f113,f117])).

fof(f113,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1553,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1552,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1552,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1523,f200])).

fof(f200,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f194,f83])).

fof(f83,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f194,plain,(
    ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f134,f152])).

fof(f152,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(resolution,[],[f139,f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

fof(f139,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK12(k1_xboole_0),X5)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(resolution,[],[f135,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK12(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK12(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f37,f69])).

fof(f69,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK12(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK12(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f96,f77])).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
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
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f134,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1523,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1149,f1501])).

fof(f1501,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f1473,f129])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1473,plain,(
    ! [X27] :
      ( ~ r1_tarski(sK1,X27)
      | k1_xboole_0 = k6_subset_1(sK0,X27) ) ),
    inference(backward_demodulation,[],[f1192,f1442])).

fof(f1442,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f1322,f121])).

fof(f1322,plain,(
    ! [X10] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10)) = X10 ),
    inference(subsumption_resolution,[],[f1304,f144])).

fof(f144,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f120,f121])).

fof(f120,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f89,f117])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1304,plain,(
    ! [X10] :
      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10)) = X10
      | ~ r1_tarski(X10,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10))) ) ),
    inference(resolution,[],[f218,f129])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)))
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f216,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f216,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))) ) ),
    inference(superposition,[],[f123,f118])).

fof(f118,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f79,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f111,f91,f117])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1192,plain,(
    ! [X27] :
      ( k1_xboole_0 = k6_subset_1(sK0,X27)
      | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(X27,X27,k1_xboole_0))) ) ),
    inference(resolution,[],[f215,f879])).

fof(f879,plain,(
    ! [X69] :
      ( r1_tarski(sK0,X69)
      | ~ r1_tarski(sK1,X69) ) ),
    inference(resolution,[],[f361,f75])).

fof(f75,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f361,plain,(
    ! [X14,X15,X13] :
      ( ~ r1_tarski(X15,X13)
      | r1_tarski(X15,X14)
      | ~ r1_tarski(X13,X14) ) ),
    inference(superposition,[],[f170,f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f305,f129])).

fof(f305,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f127,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK13(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f116,f117])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK13(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK13(X0,X1,X2))
        & r1_tarski(X2,sK13(X0,X1,X2))
        & r1_tarski(X0,sK13(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f44,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK13(X0,X1,X2))
        & r1_tarski(X2,sK13(X0,X1,X2))
        & r1_tarski(X0,sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK13(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f115,f117])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X2,sK13(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f215,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_tarski(k1_enumset1(X4,X4,k1_xboole_0)))
      | k1_xboole_0 = k6_subset_1(X3,X4) ) ),
    inference(resolution,[],[f123,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f99,f78])).

fof(f1149,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k6_subset_1(sK0,sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f381,f344])).

fof(f344,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f258,f73])).

fof(f258,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f82,f74])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f381,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k6_subset_1(X7,X5),X6)
      | r1_tarski(X7,X5)
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f124,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f318,f129])).

fof(f318,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f128,f126])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK13(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f114,f117])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK13(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f112,f117,f91])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1551,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1550,f78])).

fof(f1550,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1522,f182])).

fof(f182,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f177,f83])).

fof(f177,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f132,f152])).

fof(f132,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f58,f61,f60,f59])).

fof(f59,plain,(
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

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1522,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1146,f1501])).

fof(f1146,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k6_subset_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f381,f329])).

fof(f329,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f254,f73])).

fof(f254,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f81,f74])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (3571)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (3562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (3554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (3561)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (3548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (3552)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (3550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (3549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (3551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (3575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (3563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (3573)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (3568)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (3576)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (3565)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (3555)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (3564)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (3566)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (3567)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (3577)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (3564)Refutation not found, incomplete strategy% (3564)------------------------------
% 0.20/0.55  % (3564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3564)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3564)Memory used [KB]: 10746
% 0.20/0.55  % (3564)Time elapsed: 0.147 s
% 0.20/0.55  % (3564)------------------------------
% 0.20/0.55  % (3564)------------------------------
% 0.20/0.55  % (3574)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (3572)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (3577)Refutation not found, incomplete strategy% (3577)------------------------------
% 0.20/0.55  % (3577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (3556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (3559)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (3570)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (3557)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (3558)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (3558)Refutation not found, incomplete strategy% (3558)------------------------------
% 0.20/0.56  % (3558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (3558)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (3558)Memory used [KB]: 10746
% 0.20/0.56  % (3558)Time elapsed: 0.150 s
% 0.20/0.56  % (3558)------------------------------
% 0.20/0.56  % (3558)------------------------------
% 0.20/0.56  % (3577)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (3577)Memory used [KB]: 10746
% 0.20/0.56  % (3577)Time elapsed: 0.148 s
% 0.20/0.56  % (3577)------------------------------
% 0.20/0.56  % (3577)------------------------------
% 0.20/0.58  % (3560)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.64/0.59  % (3578)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.64/0.59  % (3553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.64/0.60  % (3578)Refutation not found, incomplete strategy% (3578)------------------------------
% 1.64/0.60  % (3578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (3578)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (3578)Memory used [KB]: 1663
% 1.64/0.60  % (3578)Time elapsed: 0.162 s
% 1.64/0.60  % (3578)------------------------------
% 1.64/0.60  % (3578)------------------------------
% 2.15/0.68  % (3571)Refutation found. Thanks to Tanya!
% 2.15/0.68  % SZS status Theorem for theBenchmark
% 2.15/0.68  % SZS output start Proof for theBenchmark
% 2.15/0.68  fof(f1602,plain,(
% 2.15/0.68    $false),
% 2.15/0.68    inference(unit_resulting_resolution,[],[f1551,f1569,f310])).
% 2.15/0.68  fof(f310,plain,(
% 2.15/0.68    ( ! [X2] : (r1_tarski(X2,k3_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK1))) )),
% 2.15/0.68    inference(superposition,[],[f170,f231])).
% 2.15/0.68  fof(f231,plain,(
% 2.15/0.68    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.15/0.68    inference(resolution,[],[f119,f74])).
% 2.15/0.68  fof(f74,plain,(
% 2.15/0.68    v1_relat_1(sK1)),
% 2.15/0.68    inference(cnf_transformation,[],[f47])).
% 2.15/0.68  fof(f47,plain,(
% 2.15/0.68    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f46,f45])).
% 2.15/0.68  fof(f45,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f46,plain,(
% 2.15/0.68    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f29,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.15/0.68    inference(flattening,[],[f28])).
% 2.15/0.68  fof(f28,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.15/0.68    inference(ennf_transformation,[],[f25])).
% 2.15/0.68  fof(f25,negated_conjecture,(
% 2.15/0.68    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.15/0.68    inference(negated_conjecture,[],[f24])).
% 2.15/0.68  fof(f24,conjecture,(
% 2.15/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 2.15/0.68  fof(f119,plain,(
% 2.15/0.68    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.15/0.68    inference(definition_unfolding,[],[f80,f117])).
% 2.15/0.68  fof(f117,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.15/0.68    inference(definition_unfolding,[],[f93,f92])).
% 2.15/0.68  fof(f92,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f14])).
% 2.15/0.68  fof(f14,axiom,(
% 2.15/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.15/0.68  fof(f93,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f15])).
% 2.15/0.68  fof(f15,axiom,(
% 2.15/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.15/0.68  fof(f80,plain,(
% 2.15/0.68    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f30])).
% 2.15/0.68  fof(f30,plain,(
% 2.15/0.68    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.15/0.68    inference(ennf_transformation,[],[f21])).
% 2.15/0.68  fof(f21,axiom,(
% 2.15/0.68    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.15/0.68  fof(f170,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_tarski(X2,X1)) )),
% 2.15/0.68    inference(superposition,[],[f122,f121])).
% 2.15/0.68  fof(f121,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f90,f92,f92])).
% 2.15/0.68  fof(f90,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f13])).
% 2.15/0.68  fof(f13,axiom,(
% 2.15/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.15/0.68  fof(f122,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f110,f117])).
% 2.15/0.68  fof(f110,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f38])).
% 2.15/0.68  fof(f38,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.15/0.68    inference(ennf_transformation,[],[f4])).
% 2.15/0.68  fof(f4,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.15/0.68  fof(f1569,plain,(
% 2.15/0.68    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.15/0.68    inference(resolution,[],[f1553,f738])).
% 2.15/0.68  fof(f738,plain,(
% 2.15/0.68    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.15/0.68    inference(resolution,[],[f725,f311])).
% 2.15/0.68  fof(f311,plain,(
% 2.15/0.68    ( ! [X3] : (r1_tarski(X3,k3_relat_1(sK1)) | ~r1_tarski(X3,k2_relat_1(sK1))) )),
% 2.15/0.68    inference(superposition,[],[f122,f231])).
% 2.15/0.68  fof(f725,plain,(
% 2.15/0.68    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.15/0.68    inference(resolution,[],[f271,f76])).
% 2.15/0.68  fof(f76,plain,(
% 2.15/0.68    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.15/0.68    inference(cnf_transformation,[],[f47])).
% 2.15/0.68  fof(f271,plain,(
% 2.15/0.68    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.15/0.68    inference(superposition,[],[f125,f230])).
% 2.15/0.68  fof(f230,plain,(
% 2.15/0.68    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.15/0.68    inference(resolution,[],[f119,f73])).
% 2.15/0.68  fof(f73,plain,(
% 2.15/0.68    v1_relat_1(sK0)),
% 2.15/0.68    inference(cnf_transformation,[],[f47])).
% 2.15/0.68  fof(f125,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f113,f117])).
% 2.15/0.68  fof(f113,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f42])).
% 2.15/0.68  fof(f42,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.15/0.68    inference(flattening,[],[f41])).
% 2.15/0.68  fof(f41,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.15/0.68    inference(ennf_transformation,[],[f12])).
% 2.15/0.68  fof(f12,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.15/0.68  fof(f1553,plain,(
% 2.15/0.68    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1552,f78])).
% 2.15/0.68  fof(f78,plain,(
% 2.15/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f6])).
% 2.15/0.68  fof(f6,axiom,(
% 2.15/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.15/0.68  fof(f1552,plain,(
% 2.15/0.68    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.15/0.68    inference(forward_demodulation,[],[f1523,f200])).
% 2.15/0.68  fof(f200,plain,(
% 2.15/0.68    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.15/0.68    inference(resolution,[],[f194,f83])).
% 2.15/0.68  fof(f83,plain,(
% 2.15/0.68    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.15/0.68    inference(cnf_transformation,[],[f49])).
% 2.15/0.68  fof(f49,plain,(
% 2.15/0.68    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f48])).
% 2.15/0.68  fof(f48,plain,(
% 2.15/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f33,plain,(
% 2.15/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.15/0.68    inference(ennf_transformation,[],[f2])).
% 2.15/0.68  fof(f2,axiom,(
% 2.15/0.68    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.15/0.68  fof(f194,plain,(
% 2.15/0.68    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0))) )),
% 2.15/0.68    inference(resolution,[],[f134,f152])).
% 2.15/0.68  fof(f152,plain,(
% 2.15/0.68    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 2.15/0.68    inference(resolution,[],[f139,f84])).
% 2.15/0.68  fof(f84,plain,(
% 2.15/0.68    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f52])).
% 2.15/0.68  fof(f52,plain,(
% 2.15/0.68    ! [X0] : (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : ((! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X6,X7] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f51,f50])).
% 2.15/0.68  fof(f50,plain,(
% 2.15/0.68    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X7,X6] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f51,plain,(
% 2.15/0.68    ! [X3,X0] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) => (! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f35,plain,(
% 2.15/0.68    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 2.15/0.68    inference(flattening,[],[f34])).
% 2.15/0.68  fof(f34,plain,(
% 2.15/0.68    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 2.15/0.68    inference(ennf_transformation,[],[f26])).
% 2.15/0.68  fof(f26,plain,(
% 2.15/0.68    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 2.15/0.68    inference(rectify,[],[f17])).
% 2.15/0.68  fof(f17,axiom,(
% 2.15/0.68    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).
% 2.15/0.68  fof(f139,plain,(
% 2.15/0.68    ( ! [X6,X5] : (~r2_hidden(sK12(k1_xboole_0),X5) | ~r2_hidden(X6,k1_xboole_0)) )),
% 2.15/0.68    inference(resolution,[],[f135,f108])).
% 2.15/0.68  fof(f108,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r2_hidden(sK12(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f70])).
% 2.15/0.68  fof(f70,plain,(
% 2.15/0.68    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK12(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK12(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f37,f69])).
% 2.15/0.68  fof(f69,plain,(
% 2.15/0.68    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK12(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK12(X1),X1)))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f37,plain,(
% 2.15/0.68    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.15/0.68    inference(ennf_transformation,[],[f16])).
% 2.15/0.68  fof(f16,axiom,(
% 2.15/0.68    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 2.15/0.68  fof(f135,plain,(
% 2.15/0.68    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 2.15/0.68    inference(resolution,[],[f96,f77])).
% 2.15/0.68  fof(f77,plain,(
% 2.15/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f10])).
% 2.15/0.68  fof(f10,axiom,(
% 2.15/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.15/0.68  fof(f96,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f54])).
% 2.15/0.68  fof(f54,plain,(
% 2.15/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f53])).
% 2.15/0.68  fof(f53,plain,(
% 2.15/0.68    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f36,plain,(
% 2.15/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.15/0.68    inference(ennf_transformation,[],[f27])).
% 2.15/0.68  fof(f27,plain,(
% 2.15/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.15/0.68    inference(rectify,[],[f1])).
% 2.15/0.68  fof(f1,axiom,(
% 2.15/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.15/0.68  fof(f134,plain,(
% 2.15/0.68    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.15/0.68    inference(equality_resolution,[],[f104])).
% 2.15/0.68  fof(f104,plain,(
% 2.15/0.68    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.15/0.68    inference(cnf_transformation,[],[f68])).
% 2.15/0.68  fof(f68,plain,(
% 2.15/0.68    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f64,f67,f66,f65])).
% 2.15/0.68  fof(f65,plain,(
% 2.15/0.68    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f66,plain,(
% 2.15/0.68    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f67,plain,(
% 2.15/0.68    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f64,plain,(
% 2.15/0.68    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.15/0.68    inference(rectify,[],[f63])).
% 2.15/0.68  fof(f63,plain,(
% 2.15/0.68    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.15/0.68    inference(nnf_transformation,[],[f20])).
% 2.15/0.68  fof(f20,axiom,(
% 2.15/0.68    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 2.15/0.68  fof(f1523,plain,(
% 2.15/0.68    ~r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1)) | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.15/0.68    inference(backward_demodulation,[],[f1149,f1501])).
% 2.15/0.68  fof(f1501,plain,(
% 2.15/0.68    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.15/0.68    inference(resolution,[],[f1473,f129])).
% 2.15/0.68  fof(f129,plain,(
% 2.15/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.15/0.68    inference(equality_resolution,[],[f98])).
% 2.15/0.68  fof(f98,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.15/0.68    inference(cnf_transformation,[],[f56])).
% 2.15/0.68  fof(f56,plain,(
% 2.15/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.68    inference(flattening,[],[f55])).
% 2.15/0.68  fof(f55,plain,(
% 2.15/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.68    inference(nnf_transformation,[],[f3])).
% 2.15/0.68  fof(f3,axiom,(
% 2.15/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.15/0.68  fof(f1473,plain,(
% 2.15/0.68    ( ! [X27] : (~r1_tarski(sK1,X27) | k1_xboole_0 = k6_subset_1(sK0,X27)) )),
% 2.15/0.68    inference(backward_demodulation,[],[f1192,f1442])).
% 2.15/0.68  fof(f1442,plain,(
% 2.15/0.68    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.15/0.68    inference(superposition,[],[f1322,f121])).
% 2.15/0.68  fof(f1322,plain,(
% 2.15/0.68    ( ! [X10] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10)) = X10) )),
% 2.15/0.68    inference(subsumption_resolution,[],[f1304,f144])).
% 2.15/0.68  fof(f144,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.15/0.68    inference(superposition,[],[f120,f121])).
% 2.15/0.68  fof(f120,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.15/0.68    inference(definition_unfolding,[],[f89,f117])).
% 2.15/0.68  fof(f89,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f11])).
% 2.15/0.68  fof(f11,axiom,(
% 2.15/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.15/0.68  fof(f1304,plain,(
% 2.15/0.68    ( ! [X10] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10)) = X10 | ~r1_tarski(X10,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X10)))) )),
% 2.15/0.68    inference(resolution,[],[f218,f129])).
% 2.15/0.68  fof(f218,plain,(
% 2.15/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 2.15/0.68    inference(resolution,[],[f216,f99])).
% 2.15/0.68  fof(f99,plain,(
% 2.15/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f56])).
% 2.15/0.68  fof(f216,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)))) )),
% 2.15/0.68    inference(superposition,[],[f123,f118])).
% 2.15/0.68  fof(f118,plain,(
% 2.15/0.68    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.15/0.68    inference(definition_unfolding,[],[f79,f91])).
% 2.15/0.68  fof(f91,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f18])).
% 2.15/0.68  fof(f18,axiom,(
% 2.15/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.15/0.68  fof(f79,plain,(
% 2.15/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.15/0.68    inference(cnf_transformation,[],[f7])).
% 2.15/0.68  fof(f7,axiom,(
% 2.15/0.68    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.15/0.68  fof(f123,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 2.15/0.68    inference(definition_unfolding,[],[f111,f91,f117])).
% 2.15/0.68  fof(f111,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f39])).
% 2.15/0.68  fof(f39,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.15/0.68    inference(ennf_transformation,[],[f8])).
% 2.15/0.68  fof(f8,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.15/0.68  fof(f1192,plain,(
% 2.15/0.68    ( ! [X27] : (k1_xboole_0 = k6_subset_1(sK0,X27) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(X27,X27,k1_xboole_0)))) )),
% 2.15/0.68    inference(resolution,[],[f215,f879])).
% 2.15/0.68  fof(f879,plain,(
% 2.15/0.68    ( ! [X69] : (r1_tarski(sK0,X69) | ~r1_tarski(sK1,X69)) )),
% 2.15/0.68    inference(resolution,[],[f361,f75])).
% 2.15/0.68  fof(f75,plain,(
% 2.15/0.68    r1_tarski(sK0,sK1)),
% 2.15/0.68    inference(cnf_transformation,[],[f47])).
% 2.15/0.68  fof(f361,plain,(
% 2.15/0.68    ( ! [X14,X15,X13] : (~r1_tarski(X15,X13) | r1_tarski(X15,X14) | ~r1_tarski(X13,X14)) )),
% 2.15/0.68    inference(superposition,[],[f170,f306])).
% 2.15/0.68  fof(f306,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(subsumption_resolution,[],[f305,f129])).
% 2.15/0.68  fof(f305,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f303])).
% 2.15/0.68  fof(f303,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(resolution,[],[f127,f126])).
% 2.15/0.68  fof(f126,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK13(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f116,f117])).
% 2.15/0.68  fof(f116,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK13(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f72])).
% 2.15/0.68  fof(f72,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK13(X0,X1,X2)) & r1_tarski(X2,sK13(X0,X1,X2)) & r1_tarski(X0,sK13(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f44,f71])).
% 2.15/0.68  fof(f71,plain,(
% 2.15/0.68    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK13(X0,X1,X2)) & r1_tarski(X2,sK13(X0,X1,X2)) & r1_tarski(X0,sK13(X0,X1,X2))))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f44,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.15/0.68    inference(flattening,[],[f43])).
% 2.15/0.68  fof(f43,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.15/0.68    inference(ennf_transformation,[],[f5])).
% 2.15/0.68  fof(f5,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.15/0.68  fof(f127,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X2,sK13(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f115,f117])).
% 2.15/0.68  fof(f115,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK13(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f72])).
% 2.15/0.68  fof(f215,plain,(
% 2.15/0.68    ( ! [X4,X3] : (~r1_tarski(X3,k3_tarski(k1_enumset1(X4,X4,k1_xboole_0))) | k1_xboole_0 = k6_subset_1(X3,X4)) )),
% 2.15/0.68    inference(resolution,[],[f123,f141])).
% 2.15/0.68  fof(f141,plain,(
% 2.15/0.68    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.15/0.68    inference(resolution,[],[f99,f78])).
% 2.15/0.68  fof(f1149,plain,(
% 2.15/0.68    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k6_subset_1(sK0,sK1)),k2_relat_1(sK1))),
% 2.15/0.68    inference(resolution,[],[f381,f344])).
% 2.15/0.68  fof(f344,plain,(
% 2.15/0.68    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 2.15/0.68    inference(resolution,[],[f258,f73])).
% 2.15/0.68  fof(f258,plain,(
% 2.15/0.68    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.15/0.68    inference(resolution,[],[f82,f74])).
% 2.15/0.68  fof(f82,plain,(
% 2.15/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f32])).
% 2.15/0.68  fof(f32,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.15/0.68    inference(ennf_transformation,[],[f23])).
% 2.15/0.68  fof(f23,axiom,(
% 2.15/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 2.15/0.68  fof(f381,plain,(
% 2.15/0.68    ( ! [X6,X7,X5] : (~r1_tarski(k6_subset_1(X7,X5),X6) | r1_tarski(X7,X5) | ~r1_tarski(X6,X5)) )),
% 2.15/0.68    inference(superposition,[],[f124,f319])).
% 2.15/0.68  fof(f319,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0)) )),
% 2.15/0.68    inference(subsumption_resolution,[],[f318,f129])).
% 2.15/0.68  fof(f318,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f316])).
% 2.15/0.68  fof(f316,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.15/0.68    inference(resolution,[],[f128,f126])).
% 2.15/0.68  fof(f128,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,sK13(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f114,f117])).
% 2.15/0.68  fof(f114,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK13(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f72])).
% 2.15/0.68  fof(f124,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.15/0.68    inference(definition_unfolding,[],[f112,f117,f91])).
% 2.15/0.68  fof(f112,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f40])).
% 2.15/0.68  fof(f40,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.15/0.68    inference(ennf_transformation,[],[f9])).
% 2.15/0.68  fof(f9,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.15/0.68  fof(f1551,plain,(
% 2.15/0.68    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1550,f78])).
% 2.15/0.68  fof(f1550,plain,(
% 2.15/0.68    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.15/0.68    inference(forward_demodulation,[],[f1522,f182])).
% 2.15/0.68  fof(f182,plain,(
% 2.15/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.15/0.68    inference(resolution,[],[f177,f83])).
% 2.15/0.68  fof(f177,plain,(
% 2.15/0.68    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0))) )),
% 2.15/0.68    inference(resolution,[],[f132,f152])).
% 2.15/0.68  fof(f132,plain,(
% 2.15/0.68    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.15/0.68    inference(equality_resolution,[],[f100])).
% 2.15/0.68  fof(f100,plain,(
% 2.15/0.68    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.15/0.69    inference(cnf_transformation,[],[f62])).
% 2.15/0.69  fof(f62,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.15/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f58,f61,f60,f59])).
% 2.15/0.69  fof(f59,plain,(
% 2.15/0.69    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f60,plain,(
% 2.15/0.69    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f61,plain,(
% 2.15/0.69    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f58,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.15/0.69    inference(rectify,[],[f57])).
% 2.15/0.69  fof(f57,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.15/0.69    inference(nnf_transformation,[],[f19])).
% 2.15/0.69  fof(f19,axiom,(
% 2.15/0.69    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.15/0.69  fof(f1522,plain,(
% 2.15/0.69    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.15/0.69    inference(backward_demodulation,[],[f1146,f1501])).
% 2.15/0.69  fof(f1146,plain,(
% 2.15/0.69    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k6_subset_1(sK0,sK1)),k1_relat_1(sK1))),
% 2.15/0.69    inference(resolution,[],[f381,f329])).
% 2.15/0.69  fof(f329,plain,(
% 2.15/0.69    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 2.15/0.69    inference(resolution,[],[f254,f73])).
% 2.15/0.69  fof(f254,plain,(
% 2.15/0.69    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.15/0.69    inference(resolution,[],[f81,f74])).
% 2.15/0.69  fof(f81,plain,(
% 2.15/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.15/0.69    inference(cnf_transformation,[],[f31])).
% 2.15/0.69  fof(f31,plain,(
% 2.15/0.69    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.15/0.69    inference(ennf_transformation,[],[f22])).
% 2.15/0.69  fof(f22,axiom,(
% 2.15/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 2.15/0.69  % SZS output end Proof for theBenchmark
% 2.15/0.69  % (3571)------------------------------
% 2.15/0.69  % (3571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.69  % (3571)Termination reason: Refutation
% 2.15/0.69  
% 2.15/0.69  % (3571)Memory used [KB]: 7931
% 2.15/0.69  % (3571)Time elapsed: 0.212 s
% 2.15/0.69  % (3571)------------------------------
% 2.15/0.69  % (3571)------------------------------
% 2.15/0.69  % (3545)Success in time 0.324 s
%------------------------------------------------------------------------------
