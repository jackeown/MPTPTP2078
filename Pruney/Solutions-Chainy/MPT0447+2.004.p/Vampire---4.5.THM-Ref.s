%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 284 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  364 (1029 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4998,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f3197,f3240,f1291])).

fof(f1291,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_relat_1(sK1))
      | ~ r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f129,f209])).

fof(f209,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f80,f123])).

fof(f123,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f87,f122])).

fof(f122,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f101,f100])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f101,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f80,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f56,f55])).

fof(f55,plain,
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

fof(f56,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f117,f122])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f3240,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f82,f3111,f232])).

fof(f232,plain,(
    ! [X2,X3] :
      ( r1_tarski(k3_relat_1(X2),X3)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | ~ r1_tarski(k1_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f132,f123])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f121,f122])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f3111,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f3110,f80])).

fof(f3110,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f3100,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3100,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f211,f1185])).

fof(f1185,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1183,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1183,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1182,f263])).

fof(f263,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f150,f150,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f71,f74,f73,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f150,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f92,f84,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f84,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f92,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(X4,sK4(X0,X2))
                | ~ r1_tarski(X4,X2) )
            & r2_hidden(sK4(X0,X2),sK3(X0)) )
          | ~ r2_hidden(X2,sK3(X0)) )
      & ! [X5,X6] :
          ( r2_hidden(X6,sK3(X0))
          | ~ r1_tarski(X6,X5)
          | ~ r2_hidden(X5,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X4,X3)
                      | ~ r1_tarski(X4,X2) )
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & ! [X5,X6] :
              ( r2_hidden(X6,X1)
              | ~ r1_tarski(X6,X5)
              | ~ r2_hidden(X5,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( r2_hidden(X4,X3)
                    | ~ r1_tarski(X4,X2) )
                & r2_hidden(X3,sK3(X0)) )
            | ~ r2_hidden(X2,sK3(X0)) )
        & ! [X6,X5] :
            ( r2_hidden(X6,sK3(X0))
            | ~ r1_tarski(X6,X5)
            | ~ r2_hidden(X5,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(X4,X3)
              | ~ r1_tarski(X4,X2) )
          & r2_hidden(X3,sK3(X0)) )
     => ( ! [X4] :
            ( r2_hidden(X4,sK4(X0,X2))
            | ~ r1_tarski(X4,X2) )
        & r2_hidden(sK4(X0,X2),sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X3)
                  | ~ r1_tarski(X4,X2) )
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X1) )
      & ! [X5,X6] :
          ( r2_hidden(X6,X1)
          | ~ r1_tarski(X6,X5)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
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
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
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
    inference(pure_predicate_removal,[],[f30])).

fof(f30,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,axiom,(
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

fof(f1182,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f255,f144])).

fof(f144,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f81,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f114,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f81,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f255,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f79,f80,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(X0)),k2_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f131,f123])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f119,f122,f99])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f82,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f3197,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f2163,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f113,f99])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f2163,plain,(
    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f2141,f90])).

fof(f2141,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1093,f1042])).

fof(f1042,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f507,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f507,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f138,f191,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK6(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f191,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f150,f136])).

fof(f136,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f138,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f83,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1093,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f244,f144])).

fof(f244,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f79,f80,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:22:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.28/0.53  % (31037)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.53  % (31036)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.56  % (31034)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.56  % (31055)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.56  % (31050)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.57  % (31043)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.57  % (31044)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.58  % (31035)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.41/0.59  % (31051)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.59  % (31054)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.59  % (31056)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.59  % (31042)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.60  % (31062)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.60  % (31039)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.60  % (31033)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.41/0.60  % (31045)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.60  % (31048)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.60  % (31041)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.61  % (31059)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.61  % (31047)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.61  % (31053)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.61  % (31060)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.61  % (31057)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.62  % (31040)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.62  % (31049)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.62  % (31038)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 2.11/0.66  % (31061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.11/0.66  % (31058)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.11/0.66  % (31052)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.11/0.67  % (31046)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.52/0.74  % (31036)Refutation not found, incomplete strategy% (31036)------------------------------
% 2.52/0.74  % (31036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.75  % (31036)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.75  
% 2.52/0.75  % (31036)Memory used [KB]: 6140
% 2.52/0.75  % (31036)Time elapsed: 0.315 s
% 2.52/0.75  % (31036)------------------------------
% 2.52/0.75  % (31036)------------------------------
% 3.40/0.83  % (31057)Time limit reached!
% 3.40/0.83  % (31057)------------------------------
% 3.40/0.83  % (31057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.83  % (31057)Termination reason: Time limit
% 3.40/0.83  
% 3.40/0.83  % (31057)Memory used [KB]: 11769
% 3.40/0.83  % (31057)Time elapsed: 0.409 s
% 3.40/0.83  % (31057)------------------------------
% 3.40/0.83  % (31057)------------------------------
% 3.72/0.88  % (31035)Time limit reached!
% 3.72/0.88  % (31035)------------------------------
% 3.72/0.88  % (31035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.88  % (31035)Termination reason: Time limit
% 3.72/0.88  
% 3.72/0.88  % (31035)Memory used [KB]: 6396
% 3.72/0.88  % (31035)Time elapsed: 0.409 s
% 3.72/0.88  % (31035)------------------------------
% 3.72/0.88  % (31035)------------------------------
% 3.72/0.88  % (31037)Refutation found. Thanks to Tanya!
% 3.72/0.88  % SZS status Theorem for theBenchmark
% 3.72/0.88  % SZS output start Proof for theBenchmark
% 3.72/0.88  fof(f4998,plain,(
% 3.72/0.88    $false),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f3197,f3240,f1291])).
% 3.72/0.88  fof(f1291,plain,(
% 3.72/0.88    ( ! [X0] : (r1_tarski(X0,k3_relat_1(sK1)) | ~r1_tarski(X0,k2_relat_1(sK1))) )),
% 3.72/0.88    inference(superposition,[],[f129,f209])).
% 3.72/0.88  fof(f209,plain,(
% 3.72/0.88    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f80,f123])).
% 3.72/0.88  fof(f123,plain,(
% 3.72/0.88    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f87,f122])).
% 3.72/0.88  fof(f122,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.72/0.88    inference(definition_unfolding,[],[f101,f100])).
% 3.72/0.88  fof(f100,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f17])).
% 3.72/0.88  fof(f17,axiom,(
% 3.72/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.72/0.88  fof(f101,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f18])).
% 3.72/0.88  fof(f18,axiom,(
% 3.72/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.72/0.88  fof(f87,plain,(
% 3.72/0.88    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f37])).
% 3.72/0.88  fof(f37,plain,(
% 3.72/0.88    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f24])).
% 3.72/0.88  fof(f24,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 3.72/0.88  fof(f80,plain,(
% 3.72/0.88    v1_relat_1(sK1)),
% 3.72/0.88    inference(cnf_transformation,[],[f57])).
% 3.72/0.88  fof(f57,plain,(
% 3.72/0.88    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f56,f55])).
% 3.72/0.88  fof(f55,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f56,plain,(
% 3.72/0.88    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f35,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.72/0.88    inference(flattening,[],[f34])).
% 3.72/0.88  fof(f34,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f29])).
% 3.72/0.88  fof(f29,negated_conjecture,(
% 3.72/0.88    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.72/0.88    inference(negated_conjecture,[],[f28])).
% 3.72/0.88  fof(f28,conjecture,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 3.72/0.88  fof(f129,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f117,f122])).
% 3.72/0.88  fof(f117,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f48])).
% 3.72/0.88  fof(f48,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.72/0.88    inference(ennf_transformation,[],[f7])).
% 3.72/0.88  fof(f7,axiom,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.72/0.88  fof(f3240,plain,(
% 3.72/0.88    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f79,f82,f3111,f232])).
% 3.72/0.88  fof(f232,plain,(
% 3.72/0.88    ( ! [X2,X3] : (r1_tarski(k3_relat_1(X2),X3) | ~r1_tarski(k2_relat_1(X2),X3) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 3.72/0.88    inference(superposition,[],[f132,f123])).
% 3.72/0.88  fof(f132,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f121,f122])).
% 3.72/0.88  fof(f121,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f54])).
% 3.72/0.88  fof(f54,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.72/0.88    inference(flattening,[],[f53])).
% 3.72/0.88  fof(f53,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.72/0.88    inference(ennf_transformation,[],[f15])).
% 3.72/0.88  fof(f15,axiom,(
% 3.72/0.88    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.72/0.88  fof(f3111,plain,(
% 3.72/0.88    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 3.72/0.88    inference(subsumption_resolution,[],[f3110,f80])).
% 3.72/0.88  fof(f3110,plain,(
% 3.72/0.88    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 3.72/0.88    inference(subsumption_resolution,[],[f3100,f85])).
% 3.72/0.88  fof(f85,plain,(
% 3.72/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f9])).
% 3.72/0.88  fof(f9,axiom,(
% 3.72/0.88    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.72/0.88  fof(f3100,plain,(
% 3.72/0.88    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 3.72/0.88    inference(superposition,[],[f211,f1185])).
% 3.72/0.88  fof(f1185,plain,(
% 3.72/0.88    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f1183,f90])).
% 3.72/0.88  fof(f90,plain,(
% 3.72/0.88    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.72/0.88    inference(cnf_transformation,[],[f40])).
% 3.72/0.88  fof(f40,plain,(
% 3.72/0.88    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.72/0.88    inference(ennf_transformation,[],[f10])).
% 3.72/0.88  fof(f10,axiom,(
% 3.72/0.88    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.72/0.88  fof(f1183,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 3.72/0.88    inference(forward_demodulation,[],[f1182,f263])).
% 3.72/0.88  fof(f263,plain,(
% 3.72/0.88    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f150,f150,f111])).
% 3.72/0.88  fof(f111,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK7(X0,X1),X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f75])).
% 3.72/0.88  fof(f75,plain,(
% 3.72/0.88    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f71,f74,f73,f72])).
% 3.72/0.88  fof(f72,plain,(
% 3.72/0.88    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f73,plain,(
% 3.72/0.88    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f74,plain,(
% 3.72/0.88    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f71,plain,(
% 3.72/0.88    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.72/0.88    inference(rectify,[],[f70])).
% 3.72/0.88  fof(f70,plain,(
% 3.72/0.88    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.72/0.88    inference(nnf_transformation,[],[f23])).
% 3.72/0.88  fof(f23,axiom,(
% 3.72/0.88    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 3.72/0.88  fof(f150,plain,(
% 3.72/0.88    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f92,f84,f104])).
% 3.72/0.88  fof(f104,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f65])).
% 3.72/0.88  fof(f65,plain,(
% 3.72/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f64])).
% 3.72/0.88  fof(f64,plain,(
% 3.72/0.88    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f44,plain,(
% 3.72/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.72/0.88    inference(ennf_transformation,[],[f32])).
% 3.72/0.88  fof(f32,plain,(
% 3.72/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.88    inference(rectify,[],[f3])).
% 3.72/0.88  fof(f3,axiom,(
% 3.72/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.72/0.88  fof(f84,plain,(
% 3.72/0.88    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f13])).
% 3.72/0.88  fof(f13,axiom,(
% 3.72/0.88    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.72/0.88  fof(f92,plain,(
% 3.72/0.88    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f63])).
% 3.72/0.88  fof(f63,plain,(
% 3.72/0.88    ! [X0] : (! [X2] : ((! [X4] : (r2_hidden(X4,sK4(X0,X2)) | ~r1_tarski(X4,X2)) & r2_hidden(sK4(X0,X2),sK3(X0))) | ~r2_hidden(X2,sK3(X0))) & ! [X5,X6] : (r2_hidden(X6,sK3(X0)) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).
% 3.72/0.88  fof(f61,plain,(
% 3.72/0.88    ! [X0] : (? [X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & ! [X5,X6] : (r2_hidden(X6,X1) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,X1)) & r2_hidden(X0,X1)) => (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,sK3(X0))) | ~r2_hidden(X2,sK3(X0))) & ! [X6,X5] : (r2_hidden(X6,sK3(X0)) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f62,plain,(
% 3.72/0.88    ! [X2,X0] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,sK3(X0))) => (! [X4] : (r2_hidden(X4,sK4(X0,X2)) | ~r1_tarski(X4,X2)) & r2_hidden(sK4(X0,X2),sK3(X0))))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f60,plain,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(X4,X3) | ~r1_tarski(X4,X2)) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X1)) & ! [X5,X6] : (r2_hidden(X6,X1) | ~r1_tarski(X6,X5) | ~r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 3.72/0.88    inference(rectify,[],[f43])).
% 3.72/0.88  fof(f43,plain,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 3.72/0.88    inference(flattening,[],[f42])).
% 3.72/0.88  fof(f42,plain,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 3.72/0.88    inference(ennf_transformation,[],[f33])).
% 3.72/0.88  fof(f33,plain,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 3.72/0.88    inference(pure_predicate_removal,[],[f30])).
% 3.72/0.88  fof(f30,plain,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 3.72/0.88    inference(rectify,[],[f20])).
% 3.72/0.88  fof(f20,axiom,(
% 3.72/0.88    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).
% 3.72/0.88  fof(f1182,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 3.72/0.88    inference(forward_demodulation,[],[f255,f144])).
% 3.72/0.88  fof(f144,plain,(
% 3.72/0.88    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f81,f127])).
% 3.72/0.88  fof(f127,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f114,f99])).
% 3.72/0.88  fof(f99,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f21])).
% 3.72/0.88  fof(f21,axiom,(
% 3.72/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.72/0.88  fof(f114,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f76])).
% 3.72/0.88  fof(f76,plain,(
% 3.72/0.88    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.72/0.88    inference(nnf_transformation,[],[f6])).
% 3.72/0.88  fof(f6,axiom,(
% 3.72/0.88    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.72/0.88  fof(f81,plain,(
% 3.72/0.88    r1_tarski(sK0,sK1)),
% 3.72/0.88    inference(cnf_transformation,[],[f57])).
% 3.72/0.88  fof(f255,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f79,f80,f89])).
% 3.72/0.88  fof(f89,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f39])).
% 3.72/0.88  fof(f39,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f25])).
% 3.72/0.88  fof(f25,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 3.72/0.88  fof(f211,plain,(
% 3.72/0.88    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(X0)),k2_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(superposition,[],[f131,f123])).
% 3.72/0.88  fof(f131,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f119,f122,f99])).
% 3.72/0.88  fof(f119,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f50])).
% 3.72/0.88  fof(f50,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.72/0.88    inference(ennf_transformation,[],[f12])).
% 3.72/0.88  fof(f12,axiom,(
% 3.72/0.88    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.72/0.88  fof(f82,plain,(
% 3.72/0.88    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 3.72/0.88    inference(cnf_transformation,[],[f57])).
% 3.72/0.88  fof(f79,plain,(
% 3.72/0.88    v1_relat_1(sK0)),
% 3.72/0.88    inference(cnf_transformation,[],[f57])).
% 3.72/0.88  fof(f3197,plain,(
% 3.72/0.88    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f2163,f128])).
% 3.72/0.88  fof(f128,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f113,f99])).
% 3.72/0.88  fof(f113,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f76])).
% 3.72/0.88  fof(f2163,plain,(
% 3.72/0.88    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f2141,f90])).
% 3.72/0.88  fof(f2141,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 3.72/0.88    inference(backward_demodulation,[],[f1093,f1042])).
% 3.72/0.88  fof(f1042,plain,(
% 3.72/0.88    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f507,f91])).
% 3.72/0.88  fof(f91,plain,(
% 3.72/0.88    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.72/0.88    inference(cnf_transformation,[],[f59])).
% 3.72/0.88  fof(f59,plain,(
% 3.72/0.88    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f58])).
% 3.72/0.88  fof(f58,plain,(
% 3.72/0.88    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f41,plain,(
% 3.72/0.88    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.72/0.88    inference(ennf_transformation,[],[f4])).
% 3.72/0.88  fof(f4,axiom,(
% 3.72/0.88    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.72/0.88  fof(f507,plain,(
% 3.72/0.88    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f138,f191,f105])).
% 3.72/0.88  fof(f105,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f67])).
% 3.72/0.88  fof(f67,plain,(
% 3.72/0.88    ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f66])).
% 3.72/0.88  fof(f66,plain,(
% 3.72/0.88    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK6(X1),k1_relat_1(X1)))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  fof(f46,plain,(
% 3.72/0.88    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.72/0.88    inference(flattening,[],[f45])).
% 3.72/0.88  fof(f45,plain,(
% 3.72/0.88    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.72/0.88    inference(ennf_transformation,[],[f26])).
% 3.72/0.88  fof(f26,axiom,(
% 3.72/0.88    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 3.72/0.88  fof(f191,plain,(
% 3.72/0.88    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f150,f136])).
% 3.72/0.88  fof(f136,plain,(
% 3.72/0.88    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.72/0.88    inference(equality_resolution,[],[f109])).
% 3.72/0.88  fof(f109,plain,(
% 3.72/0.88    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.72/0.88    inference(cnf_transformation,[],[f75])).
% 3.72/0.88  fof(f138,plain,(
% 3.72/0.88    v1_relat_1(k1_xboole_0)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f83,f86])).
% 3.72/0.88  fof(f86,plain,(
% 3.72/0.88    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f36])).
% 3.72/0.88  fof(f36,plain,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f22])).
% 3.72/0.88  fof(f22,axiom,(
% 3.72/0.88    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 3.72/0.88  fof(f83,plain,(
% 3.72/0.88    v1_xboole_0(k1_xboole_0)),
% 3.72/0.88    inference(cnf_transformation,[],[f1])).
% 3.72/0.88  fof(f1,axiom,(
% 3.72/0.88    v1_xboole_0(k1_xboole_0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.72/0.88  fof(f1093,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 3.72/0.88    inference(forward_demodulation,[],[f244,f144])).
% 3.72/0.88  fof(f244,plain,(
% 3.72/0.88    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f79,f80,f88])).
% 3.72/0.88  fof(f88,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f38])).
% 3.72/0.88  fof(f38,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f27])).
% 3.72/0.88  fof(f27,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 3.72/0.88  % SZS output end Proof for theBenchmark
% 3.72/0.88  % (31037)------------------------------
% 3.72/0.88  % (31037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.88  % (31037)Termination reason: Refutation
% 3.72/0.88  
% 3.72/0.89  % (31037)Memory used [KB]: 4221
% 3.72/0.89  % (31037)Time elapsed: 0.424 s
% 3.72/0.89  % (31037)------------------------------
% 3.72/0.89  % (31037)------------------------------
% 3.72/0.89  % (31032)Success in time 0.521 s
%------------------------------------------------------------------------------
