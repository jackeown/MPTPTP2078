%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:27 EST 2020

% Result     : Theorem 7.30s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 195 expanded)
%              Number of clauses        :   55 (  60 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 816 expanded)
%              Number of equality atoms :   88 ( 152 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f34])).

fof(f55,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f57,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10063,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(X0,k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_23305,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_10063])).

cnf(c_5038,plain,
    ( ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),X0)
    | ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r1_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5891,plain,
    ( ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
    | ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_5038])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),X1) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_4012,plain,
    ( r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_4014,plain,
    ( r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_277,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_265,c_13])).

cnf(c_1365,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_2509,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1204,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1200,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2123,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1200])).

cnf(c_2207,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_2123])).

cnf(c_2238,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2207])).

cnf(c_2240,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_773,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2065,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | k10_relat_1(sK6,sK5) != X0
    | k10_relat_1(sK6,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_2067,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2062,plain,
    ( r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5))
    | r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_772,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1538,plain,
    ( X0 != X1
    | k10_relat_1(sK6,sK5) != X1
    | k10_relat_1(sK6,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1754,plain,
    ( X0 != k10_relat_1(sK6,sK5)
    | k10_relat_1(sK6,sK5) = X0
    | k10_relat_1(sK6,sK5) != k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_1756,plain,
    ( k10_relat_1(sK6,sK5) != k10_relat_1(sK6,sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1532,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK6,sK5))
    | ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
    | k10_relat_1(sK6,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1750,plain,
    ( ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | k10_relat_1(sK6,sK5) = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1468,plain,
    ( ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
    | ~ r1_tarski(k10_relat_1(sK6,sK5),X1)
    | ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1565,plain,
    ( ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
    | ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_1711,plain,
    ( ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1566,plain,
    ( r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1393,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1340,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1337,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23305,c_5891,c_4012,c_4014,c_2509,c_2240,c_2067,c_2062,c_1756,c_1750,c_1711,c_1566,c_1393,c_1340,c_1337,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.30/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/1.51  
% 7.30/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.30/1.51  
% 7.30/1.51  ------  iProver source info
% 7.30/1.51  
% 7.30/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.30/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.30/1.51  git: non_committed_changes: false
% 7.30/1.51  git: last_make_outside_of_git: false
% 7.30/1.51  
% 7.30/1.51  ------ 
% 7.30/1.51  
% 7.30/1.51  ------ Input Options
% 7.30/1.51  
% 7.30/1.51  --out_options                           all
% 7.30/1.51  --tptp_safe_out                         true
% 7.30/1.51  --problem_path                          ""
% 7.30/1.51  --include_path                          ""
% 7.30/1.51  --clausifier                            res/vclausify_rel
% 7.30/1.51  --clausifier_options                    --mode clausify
% 7.30/1.51  --stdin                                 false
% 7.30/1.51  --stats_out                             all
% 7.30/1.51  
% 7.30/1.51  ------ General Options
% 7.30/1.51  
% 7.30/1.51  --fof                                   false
% 7.30/1.51  --time_out_real                         305.
% 7.30/1.51  --time_out_virtual                      -1.
% 7.30/1.51  --symbol_type_check                     false
% 7.30/1.51  --clausify_out                          false
% 7.30/1.51  --sig_cnt_out                           false
% 7.30/1.51  --trig_cnt_out                          false
% 7.30/1.51  --trig_cnt_out_tolerance                1.
% 7.30/1.51  --trig_cnt_out_sk_spl                   false
% 7.30/1.51  --abstr_cl_out                          false
% 7.30/1.51  
% 7.30/1.51  ------ Global Options
% 7.30/1.51  
% 7.30/1.51  --schedule                              default
% 7.30/1.51  --add_important_lit                     false
% 7.30/1.51  --prop_solver_per_cl                    1000
% 7.30/1.51  --min_unsat_core                        false
% 7.30/1.51  --soft_assumptions                      false
% 7.30/1.51  --soft_lemma_size                       3
% 7.30/1.51  --prop_impl_unit_size                   0
% 7.30/1.51  --prop_impl_unit                        []
% 7.30/1.51  --share_sel_clauses                     true
% 7.30/1.51  --reset_solvers                         false
% 7.30/1.51  --bc_imp_inh                            [conj_cone]
% 7.30/1.51  --conj_cone_tolerance                   3.
% 7.30/1.51  --extra_neg_conj                        none
% 7.30/1.51  --large_theory_mode                     true
% 7.30/1.51  --prolific_symb_bound                   200
% 7.30/1.51  --lt_threshold                          2000
% 7.30/1.51  --clause_weak_htbl                      true
% 7.30/1.51  --gc_record_bc_elim                     false
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing Options
% 7.30/1.51  
% 7.30/1.51  --preprocessing_flag                    true
% 7.30/1.51  --time_out_prep_mult                    0.1
% 7.30/1.51  --splitting_mode                        input
% 7.30/1.51  --splitting_grd                         true
% 7.30/1.51  --splitting_cvd                         false
% 7.30/1.51  --splitting_cvd_svl                     false
% 7.30/1.51  --splitting_nvd                         32
% 7.30/1.51  --sub_typing                            true
% 7.30/1.51  --prep_gs_sim                           true
% 7.30/1.51  --prep_unflatten                        true
% 7.30/1.51  --prep_res_sim                          true
% 7.30/1.51  --prep_upred                            true
% 7.30/1.51  --prep_sem_filter                       exhaustive
% 7.30/1.51  --prep_sem_filter_out                   false
% 7.30/1.51  --pred_elim                             true
% 7.30/1.51  --res_sim_input                         true
% 7.30/1.51  --eq_ax_congr_red                       true
% 7.30/1.51  --pure_diseq_elim                       true
% 7.30/1.51  --brand_transform                       false
% 7.30/1.51  --non_eq_to_eq                          false
% 7.30/1.51  --prep_def_merge                        true
% 7.30/1.51  --prep_def_merge_prop_impl              false
% 7.30/1.51  --prep_def_merge_mbd                    true
% 7.30/1.51  --prep_def_merge_tr_red                 false
% 7.30/1.51  --prep_def_merge_tr_cl                  false
% 7.30/1.51  --smt_preprocessing                     true
% 7.30/1.51  --smt_ac_axioms                         fast
% 7.30/1.51  --preprocessed_out                      false
% 7.30/1.51  --preprocessed_stats                    false
% 7.30/1.51  
% 7.30/1.51  ------ Abstraction refinement Options
% 7.30/1.51  
% 7.30/1.51  --abstr_ref                             []
% 7.30/1.51  --abstr_ref_prep                        false
% 7.30/1.51  --abstr_ref_until_sat                   false
% 7.30/1.51  --abstr_ref_sig_restrict                funpre
% 7.30/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.30/1.51  --abstr_ref_under                       []
% 7.30/1.51  
% 7.30/1.51  ------ SAT Options
% 7.30/1.51  
% 7.30/1.51  --sat_mode                              false
% 7.30/1.51  --sat_fm_restart_options                ""
% 7.30/1.51  --sat_gr_def                            false
% 7.30/1.51  --sat_epr_types                         true
% 7.30/1.51  --sat_non_cyclic_types                  false
% 7.30/1.51  --sat_finite_models                     false
% 7.30/1.51  --sat_fm_lemmas                         false
% 7.30/1.51  --sat_fm_prep                           false
% 7.30/1.51  --sat_fm_uc_incr                        true
% 7.30/1.51  --sat_out_model                         small
% 7.30/1.51  --sat_out_clauses                       false
% 7.30/1.51  
% 7.30/1.51  ------ QBF Options
% 7.30/1.51  
% 7.30/1.51  --qbf_mode                              false
% 7.30/1.51  --qbf_elim_univ                         false
% 7.30/1.51  --qbf_dom_inst                          none
% 7.30/1.51  --qbf_dom_pre_inst                      false
% 7.30/1.51  --qbf_sk_in                             false
% 7.30/1.51  --qbf_pred_elim                         true
% 7.30/1.51  --qbf_split                             512
% 7.30/1.51  
% 7.30/1.51  ------ BMC1 Options
% 7.30/1.51  
% 7.30/1.51  --bmc1_incremental                      false
% 7.30/1.51  --bmc1_axioms                           reachable_all
% 7.30/1.51  --bmc1_min_bound                        0
% 7.30/1.51  --bmc1_max_bound                        -1
% 7.30/1.51  --bmc1_max_bound_default                -1
% 7.30/1.51  --bmc1_symbol_reachability              true
% 7.30/1.51  --bmc1_property_lemmas                  false
% 7.30/1.51  --bmc1_k_induction                      false
% 7.30/1.51  --bmc1_non_equiv_states                 false
% 7.30/1.51  --bmc1_deadlock                         false
% 7.30/1.51  --bmc1_ucm                              false
% 7.30/1.51  --bmc1_add_unsat_core                   none
% 7.30/1.51  --bmc1_unsat_core_children              false
% 7.30/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.30/1.51  --bmc1_out_stat                         full
% 7.30/1.51  --bmc1_ground_init                      false
% 7.30/1.51  --bmc1_pre_inst_next_state              false
% 7.30/1.51  --bmc1_pre_inst_state                   false
% 7.30/1.51  --bmc1_pre_inst_reach_state             false
% 7.30/1.51  --bmc1_out_unsat_core                   false
% 7.30/1.51  --bmc1_aig_witness_out                  false
% 7.30/1.51  --bmc1_verbose                          false
% 7.30/1.51  --bmc1_dump_clauses_tptp                false
% 7.30/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.30/1.51  --bmc1_dump_file                        -
% 7.30/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.30/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.30/1.51  --bmc1_ucm_extend_mode                  1
% 7.30/1.51  --bmc1_ucm_init_mode                    2
% 7.30/1.51  --bmc1_ucm_cone_mode                    none
% 7.30/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.30/1.51  --bmc1_ucm_relax_model                  4
% 7.30/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.30/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.30/1.51  --bmc1_ucm_layered_model                none
% 7.30/1.51  --bmc1_ucm_max_lemma_size               10
% 7.30/1.51  
% 7.30/1.51  ------ AIG Options
% 7.30/1.51  
% 7.30/1.51  --aig_mode                              false
% 7.30/1.51  
% 7.30/1.51  ------ Instantiation Options
% 7.30/1.51  
% 7.30/1.51  --instantiation_flag                    true
% 7.30/1.51  --inst_sos_flag                         false
% 7.30/1.51  --inst_sos_phase                        true
% 7.30/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.30/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.30/1.51  --inst_lit_sel_side                     num_symb
% 7.30/1.51  --inst_solver_per_active                1400
% 7.30/1.51  --inst_solver_calls_frac                1.
% 7.30/1.51  --inst_passive_queue_type               priority_queues
% 7.30/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.30/1.51  --inst_passive_queues_freq              [25;2]
% 7.30/1.51  --inst_dismatching                      true
% 7.30/1.51  --inst_eager_unprocessed_to_passive     true
% 7.30/1.51  --inst_prop_sim_given                   true
% 7.30/1.51  --inst_prop_sim_new                     false
% 7.30/1.51  --inst_subs_new                         false
% 7.30/1.51  --inst_eq_res_simp                      false
% 7.30/1.51  --inst_subs_given                       false
% 7.30/1.51  --inst_orphan_elimination               true
% 7.30/1.51  --inst_learning_loop_flag               true
% 7.30/1.51  --inst_learning_start                   3000
% 7.30/1.51  --inst_learning_factor                  2
% 7.30/1.51  --inst_start_prop_sim_after_learn       3
% 7.30/1.51  --inst_sel_renew                        solver
% 7.30/1.51  --inst_lit_activity_flag                true
% 7.30/1.51  --inst_restr_to_given                   false
% 7.30/1.51  --inst_activity_threshold               500
% 7.30/1.51  --inst_out_proof                        true
% 7.30/1.51  
% 7.30/1.51  ------ Resolution Options
% 7.30/1.51  
% 7.30/1.51  --resolution_flag                       true
% 7.30/1.51  --res_lit_sel                           adaptive
% 7.30/1.51  --res_lit_sel_side                      none
% 7.30/1.51  --res_ordering                          kbo
% 7.30/1.51  --res_to_prop_solver                    active
% 7.30/1.51  --res_prop_simpl_new                    false
% 7.30/1.51  --res_prop_simpl_given                  true
% 7.30/1.51  --res_passive_queue_type                priority_queues
% 7.30/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.30/1.51  --res_passive_queues_freq               [15;5]
% 7.30/1.51  --res_forward_subs                      full
% 7.30/1.51  --res_backward_subs                     full
% 7.30/1.51  --res_forward_subs_resolution           true
% 7.30/1.51  --res_backward_subs_resolution          true
% 7.30/1.51  --res_orphan_elimination                true
% 7.30/1.51  --res_time_limit                        2.
% 7.30/1.51  --res_out_proof                         true
% 7.30/1.51  
% 7.30/1.51  ------ Superposition Options
% 7.30/1.51  
% 7.30/1.51  --superposition_flag                    true
% 7.30/1.51  --sup_passive_queue_type                priority_queues
% 7.30/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.30/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.30/1.51  --demod_completeness_check              fast
% 7.30/1.51  --demod_use_ground                      true
% 7.30/1.51  --sup_to_prop_solver                    passive
% 7.30/1.51  --sup_prop_simpl_new                    true
% 7.30/1.51  --sup_prop_simpl_given                  true
% 7.30/1.51  --sup_fun_splitting                     false
% 7.30/1.51  --sup_smt_interval                      50000
% 7.30/1.51  
% 7.30/1.51  ------ Superposition Simplification Setup
% 7.30/1.51  
% 7.30/1.51  --sup_indices_passive                   []
% 7.30/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.30/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_full_bw                           [BwDemod]
% 7.30/1.51  --sup_immed_triv                        [TrivRules]
% 7.30/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.30/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_immed_bw_main                     []
% 7.30/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.30/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.30/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.30/1.51  
% 7.30/1.51  ------ Combination Options
% 7.30/1.51  
% 7.30/1.51  --comb_res_mult                         3
% 7.30/1.51  --comb_sup_mult                         2
% 7.30/1.51  --comb_inst_mult                        10
% 7.30/1.51  
% 7.30/1.51  ------ Debug Options
% 7.30/1.51  
% 7.30/1.51  --dbg_backtrace                         false
% 7.30/1.51  --dbg_dump_prop_clauses                 false
% 7.30/1.51  --dbg_dump_prop_clauses_file            -
% 7.30/1.51  --dbg_out_stat                          false
% 7.30/1.51  ------ Parsing...
% 7.30/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.30/1.51  ------ Proving...
% 7.30/1.51  ------ Problem Properties 
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  clauses                                 20
% 7.30/1.51  conjectures                             2
% 7.30/1.51  EPR                                     4
% 7.30/1.51  Horn                                    15
% 7.30/1.51  unary                                   4
% 7.30/1.51  binary                                  9
% 7.30/1.51  lits                                    44
% 7.30/1.51  lits eq                                 11
% 7.30/1.51  fd_pure                                 0
% 7.30/1.51  fd_pseudo                               0
% 7.30/1.51  fd_cond                                 2
% 7.30/1.51  fd_pseudo_cond                          3
% 7.30/1.51  AC symbols                              0
% 7.30/1.51  
% 7.30/1.51  ------ Schedule dynamic 5 is on 
% 7.30/1.51  
% 7.30/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  ------ 
% 7.30/1.51  Current options:
% 7.30/1.51  ------ 
% 7.30/1.51  
% 7.30/1.51  ------ Input Options
% 7.30/1.51  
% 7.30/1.51  --out_options                           all
% 7.30/1.51  --tptp_safe_out                         true
% 7.30/1.51  --problem_path                          ""
% 7.30/1.51  --include_path                          ""
% 7.30/1.51  --clausifier                            res/vclausify_rel
% 7.30/1.51  --clausifier_options                    --mode clausify
% 7.30/1.51  --stdin                                 false
% 7.30/1.51  --stats_out                             all
% 7.30/1.51  
% 7.30/1.51  ------ General Options
% 7.30/1.51  
% 7.30/1.51  --fof                                   false
% 7.30/1.51  --time_out_real                         305.
% 7.30/1.51  --time_out_virtual                      -1.
% 7.30/1.51  --symbol_type_check                     false
% 7.30/1.51  --clausify_out                          false
% 7.30/1.51  --sig_cnt_out                           false
% 7.30/1.51  --trig_cnt_out                          false
% 7.30/1.51  --trig_cnt_out_tolerance                1.
% 7.30/1.51  --trig_cnt_out_sk_spl                   false
% 7.30/1.51  --abstr_cl_out                          false
% 7.30/1.51  
% 7.30/1.51  ------ Global Options
% 7.30/1.51  
% 7.30/1.51  --schedule                              default
% 7.30/1.51  --add_important_lit                     false
% 7.30/1.51  --prop_solver_per_cl                    1000
% 7.30/1.51  --min_unsat_core                        false
% 7.30/1.51  --soft_assumptions                      false
% 7.30/1.51  --soft_lemma_size                       3
% 7.30/1.51  --prop_impl_unit_size                   0
% 7.30/1.51  --prop_impl_unit                        []
% 7.30/1.51  --share_sel_clauses                     true
% 7.30/1.51  --reset_solvers                         false
% 7.30/1.51  --bc_imp_inh                            [conj_cone]
% 7.30/1.51  --conj_cone_tolerance                   3.
% 7.30/1.51  --extra_neg_conj                        none
% 7.30/1.51  --large_theory_mode                     true
% 7.30/1.51  --prolific_symb_bound                   200
% 7.30/1.51  --lt_threshold                          2000
% 7.30/1.51  --clause_weak_htbl                      true
% 7.30/1.51  --gc_record_bc_elim                     false
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing Options
% 7.30/1.51  
% 7.30/1.51  --preprocessing_flag                    true
% 7.30/1.51  --time_out_prep_mult                    0.1
% 7.30/1.51  --splitting_mode                        input
% 7.30/1.51  --splitting_grd                         true
% 7.30/1.51  --splitting_cvd                         false
% 7.30/1.51  --splitting_cvd_svl                     false
% 7.30/1.51  --splitting_nvd                         32
% 7.30/1.51  --sub_typing                            true
% 7.30/1.51  --prep_gs_sim                           true
% 7.30/1.51  --prep_unflatten                        true
% 7.30/1.51  --prep_res_sim                          true
% 7.30/1.51  --prep_upred                            true
% 7.30/1.51  --prep_sem_filter                       exhaustive
% 7.30/1.51  --prep_sem_filter_out                   false
% 7.30/1.51  --pred_elim                             true
% 7.30/1.51  --res_sim_input                         true
% 7.30/1.51  --eq_ax_congr_red                       true
% 7.30/1.51  --pure_diseq_elim                       true
% 7.30/1.51  --brand_transform                       false
% 7.30/1.51  --non_eq_to_eq                          false
% 7.30/1.51  --prep_def_merge                        true
% 7.30/1.51  --prep_def_merge_prop_impl              false
% 7.30/1.51  --prep_def_merge_mbd                    true
% 7.30/1.51  --prep_def_merge_tr_red                 false
% 7.30/1.51  --prep_def_merge_tr_cl                  false
% 7.30/1.51  --smt_preprocessing                     true
% 7.30/1.51  --smt_ac_axioms                         fast
% 7.30/1.51  --preprocessed_out                      false
% 7.30/1.51  --preprocessed_stats                    false
% 7.30/1.51  
% 7.30/1.51  ------ Abstraction refinement Options
% 7.30/1.51  
% 7.30/1.51  --abstr_ref                             []
% 7.30/1.51  --abstr_ref_prep                        false
% 7.30/1.51  --abstr_ref_until_sat                   false
% 7.30/1.51  --abstr_ref_sig_restrict                funpre
% 7.30/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.30/1.51  --abstr_ref_under                       []
% 7.30/1.51  
% 7.30/1.51  ------ SAT Options
% 7.30/1.51  
% 7.30/1.51  --sat_mode                              false
% 7.30/1.51  --sat_fm_restart_options                ""
% 7.30/1.51  --sat_gr_def                            false
% 7.30/1.51  --sat_epr_types                         true
% 7.30/1.51  --sat_non_cyclic_types                  false
% 7.30/1.51  --sat_finite_models                     false
% 7.30/1.51  --sat_fm_lemmas                         false
% 7.30/1.51  --sat_fm_prep                           false
% 7.30/1.51  --sat_fm_uc_incr                        true
% 7.30/1.51  --sat_out_model                         small
% 7.30/1.51  --sat_out_clauses                       false
% 7.30/1.51  
% 7.30/1.51  ------ QBF Options
% 7.30/1.51  
% 7.30/1.51  --qbf_mode                              false
% 7.30/1.51  --qbf_elim_univ                         false
% 7.30/1.51  --qbf_dom_inst                          none
% 7.30/1.51  --qbf_dom_pre_inst                      false
% 7.30/1.51  --qbf_sk_in                             false
% 7.30/1.51  --qbf_pred_elim                         true
% 7.30/1.51  --qbf_split                             512
% 7.30/1.51  
% 7.30/1.51  ------ BMC1 Options
% 7.30/1.51  
% 7.30/1.51  --bmc1_incremental                      false
% 7.30/1.51  --bmc1_axioms                           reachable_all
% 7.30/1.51  --bmc1_min_bound                        0
% 7.30/1.51  --bmc1_max_bound                        -1
% 7.30/1.51  --bmc1_max_bound_default                -1
% 7.30/1.51  --bmc1_symbol_reachability              true
% 7.30/1.51  --bmc1_property_lemmas                  false
% 7.30/1.51  --bmc1_k_induction                      false
% 7.30/1.51  --bmc1_non_equiv_states                 false
% 7.30/1.51  --bmc1_deadlock                         false
% 7.30/1.51  --bmc1_ucm                              false
% 7.30/1.51  --bmc1_add_unsat_core                   none
% 7.30/1.51  --bmc1_unsat_core_children              false
% 7.30/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.30/1.51  --bmc1_out_stat                         full
% 7.30/1.51  --bmc1_ground_init                      false
% 7.30/1.51  --bmc1_pre_inst_next_state              false
% 7.30/1.51  --bmc1_pre_inst_state                   false
% 7.30/1.51  --bmc1_pre_inst_reach_state             false
% 7.30/1.51  --bmc1_out_unsat_core                   false
% 7.30/1.51  --bmc1_aig_witness_out                  false
% 7.30/1.51  --bmc1_verbose                          false
% 7.30/1.51  --bmc1_dump_clauses_tptp                false
% 7.30/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.30/1.51  --bmc1_dump_file                        -
% 7.30/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.30/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.30/1.51  --bmc1_ucm_extend_mode                  1
% 7.30/1.51  --bmc1_ucm_init_mode                    2
% 7.30/1.51  --bmc1_ucm_cone_mode                    none
% 7.30/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.30/1.51  --bmc1_ucm_relax_model                  4
% 7.30/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.30/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.30/1.51  --bmc1_ucm_layered_model                none
% 7.30/1.51  --bmc1_ucm_max_lemma_size               10
% 7.30/1.51  
% 7.30/1.51  ------ AIG Options
% 7.30/1.51  
% 7.30/1.51  --aig_mode                              false
% 7.30/1.51  
% 7.30/1.51  ------ Instantiation Options
% 7.30/1.51  
% 7.30/1.51  --instantiation_flag                    true
% 7.30/1.51  --inst_sos_flag                         false
% 7.30/1.51  --inst_sos_phase                        true
% 7.30/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.30/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.30/1.51  --inst_lit_sel_side                     none
% 7.30/1.51  --inst_solver_per_active                1400
% 7.30/1.51  --inst_solver_calls_frac                1.
% 7.30/1.51  --inst_passive_queue_type               priority_queues
% 7.30/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.30/1.51  --inst_passive_queues_freq              [25;2]
% 7.30/1.51  --inst_dismatching                      true
% 7.30/1.51  --inst_eager_unprocessed_to_passive     true
% 7.30/1.51  --inst_prop_sim_given                   true
% 7.30/1.51  --inst_prop_sim_new                     false
% 7.30/1.51  --inst_subs_new                         false
% 7.30/1.51  --inst_eq_res_simp                      false
% 7.30/1.51  --inst_subs_given                       false
% 7.30/1.51  --inst_orphan_elimination               true
% 7.30/1.51  --inst_learning_loop_flag               true
% 7.30/1.51  --inst_learning_start                   3000
% 7.30/1.51  --inst_learning_factor                  2
% 7.30/1.51  --inst_start_prop_sim_after_learn       3
% 7.30/1.51  --inst_sel_renew                        solver
% 7.30/1.51  --inst_lit_activity_flag                true
% 7.30/1.51  --inst_restr_to_given                   false
% 7.30/1.51  --inst_activity_threshold               500
% 7.30/1.51  --inst_out_proof                        true
% 7.30/1.51  
% 7.30/1.51  ------ Resolution Options
% 7.30/1.51  
% 7.30/1.51  --resolution_flag                       false
% 7.30/1.51  --res_lit_sel                           adaptive
% 7.30/1.51  --res_lit_sel_side                      none
% 7.30/1.51  --res_ordering                          kbo
% 7.30/1.51  --res_to_prop_solver                    active
% 7.30/1.51  --res_prop_simpl_new                    false
% 7.30/1.51  --res_prop_simpl_given                  true
% 7.30/1.51  --res_passive_queue_type                priority_queues
% 7.30/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.30/1.51  --res_passive_queues_freq               [15;5]
% 7.30/1.51  --res_forward_subs                      full
% 7.30/1.51  --res_backward_subs                     full
% 7.30/1.51  --res_forward_subs_resolution           true
% 7.30/1.51  --res_backward_subs_resolution          true
% 7.30/1.51  --res_orphan_elimination                true
% 7.30/1.51  --res_time_limit                        2.
% 7.30/1.51  --res_out_proof                         true
% 7.30/1.51  
% 7.30/1.51  ------ Superposition Options
% 7.30/1.51  
% 7.30/1.51  --superposition_flag                    true
% 7.30/1.51  --sup_passive_queue_type                priority_queues
% 7.30/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.30/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.30/1.51  --demod_completeness_check              fast
% 7.30/1.51  --demod_use_ground                      true
% 7.30/1.51  --sup_to_prop_solver                    passive
% 7.30/1.51  --sup_prop_simpl_new                    true
% 7.30/1.51  --sup_prop_simpl_given                  true
% 7.30/1.51  --sup_fun_splitting                     false
% 7.30/1.51  --sup_smt_interval                      50000
% 7.30/1.51  
% 7.30/1.51  ------ Superposition Simplification Setup
% 7.30/1.51  
% 7.30/1.51  --sup_indices_passive                   []
% 7.30/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.30/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.30/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_full_bw                           [BwDemod]
% 7.30/1.51  --sup_immed_triv                        [TrivRules]
% 7.30/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.30/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_immed_bw_main                     []
% 7.30/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.30/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.30/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.30/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.30/1.51  
% 7.30/1.51  ------ Combination Options
% 7.30/1.51  
% 7.30/1.51  --comb_res_mult                         3
% 7.30/1.51  --comb_sup_mult                         2
% 7.30/1.51  --comb_inst_mult                        10
% 7.30/1.51  
% 7.30/1.51  ------ Debug Options
% 7.30/1.51  
% 7.30/1.51  --dbg_backtrace                         false
% 7.30/1.51  --dbg_dump_prop_clauses                 false
% 7.30/1.51  --dbg_dump_prop_clauses_file            -
% 7.30/1.51  --dbg_out_stat                          false
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  ------ Proving...
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  % SZS status Theorem for theBenchmark.p
% 7.30/1.51  
% 7.30/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.30/1.51  
% 7.30/1.51  fof(f1,axiom,(
% 7.30/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f10,plain,(
% 7.30/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.30/1.51    inference(rectify,[],[f1])).
% 7.30/1.51  
% 7.30/1.51  fof(f11,plain,(
% 7.30/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.30/1.51    inference(ennf_transformation,[],[f10])).
% 7.30/1.51  
% 7.30/1.51  fof(f16,plain,(
% 7.30/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f17,plain,(
% 7.30/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.30/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 7.30/1.51  
% 7.30/1.51  fof(f38,plain,(
% 7.30/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f17])).
% 7.30/1.51  
% 7.30/1.51  fof(f7,axiom,(
% 7.30/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f14,plain,(
% 7.30/1.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.30/1.51    inference(ennf_transformation,[],[f7])).
% 7.30/1.51  
% 7.30/1.51  fof(f28,plain,(
% 7.30/1.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.30/1.51    inference(nnf_transformation,[],[f14])).
% 7.30/1.51  
% 7.30/1.51  fof(f29,plain,(
% 7.30/1.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.30/1.51    inference(rectify,[],[f28])).
% 7.30/1.51  
% 7.30/1.51  fof(f30,plain,(
% 7.30/1.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f31,plain,(
% 7.30/1.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.30/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 7.30/1.51  
% 7.30/1.51  fof(f53,plain,(
% 7.30/1.51    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f31])).
% 7.30/1.51  
% 7.30/1.51  fof(f8,conjecture,(
% 7.30/1.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f9,negated_conjecture,(
% 7.30/1.51    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.30/1.51    inference(negated_conjecture,[],[f8])).
% 7.30/1.51  
% 7.30/1.51  fof(f15,plain,(
% 7.30/1.51    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.30/1.51    inference(ennf_transformation,[],[f9])).
% 7.30/1.51  
% 7.30/1.51  fof(f32,plain,(
% 7.30/1.51    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.30/1.51    inference(nnf_transformation,[],[f15])).
% 7.30/1.51  
% 7.30/1.51  fof(f33,plain,(
% 7.30/1.51    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.30/1.51    inference(flattening,[],[f32])).
% 7.30/1.51  
% 7.30/1.51  fof(f34,plain,(
% 7.30/1.51    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f35,plain,(
% 7.30/1.51    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 7.30/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f34])).
% 7.30/1.51  
% 7.30/1.51  fof(f55,plain,(
% 7.30/1.51    v1_relat_1(sK6)),
% 7.30/1.51    inference(cnf_transformation,[],[f35])).
% 7.30/1.51  
% 7.30/1.51  fof(f51,plain,(
% 7.30/1.51    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f31])).
% 7.30/1.51  
% 7.30/1.51  fof(f54,plain,(
% 7.30/1.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f31])).
% 7.30/1.51  
% 7.30/1.51  fof(f6,axiom,(
% 7.30/1.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f22,plain,(
% 7.30/1.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.30/1.51    inference(nnf_transformation,[],[f6])).
% 7.30/1.51  
% 7.30/1.51  fof(f23,plain,(
% 7.30/1.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.30/1.51    inference(rectify,[],[f22])).
% 7.30/1.51  
% 7.30/1.51  fof(f26,plain,(
% 7.30/1.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f25,plain,(
% 7.30/1.51    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f24,plain,(
% 7.30/1.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.30/1.51    introduced(choice_axiom,[])).
% 7.30/1.51  
% 7.30/1.51  fof(f27,plain,(
% 7.30/1.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.30/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 7.30/1.51  
% 7.30/1.51  fof(f48,plain,(
% 7.30/1.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 7.30/1.51    inference(cnf_transformation,[],[f27])).
% 7.30/1.51  
% 7.30/1.51  fof(f62,plain,(
% 7.30/1.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 7.30/1.51    inference(equality_resolution,[],[f48])).
% 7.30/1.51  
% 7.30/1.51  fof(f36,plain,(
% 7.30/1.51    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f17])).
% 7.30/1.51  
% 7.30/1.51  fof(f4,axiom,(
% 7.30/1.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f20,plain,(
% 7.30/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.30/1.51    inference(nnf_transformation,[],[f4])).
% 7.30/1.51  
% 7.30/1.51  fof(f21,plain,(
% 7.30/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.30/1.51    inference(flattening,[],[f20])).
% 7.30/1.51  
% 7.30/1.51  fof(f45,plain,(
% 7.30/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.30/1.51    inference(cnf_transformation,[],[f21])).
% 7.30/1.51  
% 7.30/1.51  fof(f60,plain,(
% 7.30/1.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.30/1.51    inference(equality_resolution,[],[f45])).
% 7.30/1.51  
% 7.30/1.51  fof(f5,axiom,(
% 7.30/1.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f46,plain,(
% 7.30/1.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 7.30/1.51    inference(cnf_transformation,[],[f5])).
% 7.30/1.51  
% 7.30/1.51  fof(f37,plain,(
% 7.30/1.51    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f17])).
% 7.30/1.51  
% 7.30/1.51  fof(f2,axiom,(
% 7.30/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f18,plain,(
% 7.30/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.30/1.51    inference(nnf_transformation,[],[f2])).
% 7.30/1.51  
% 7.30/1.51  fof(f19,plain,(
% 7.30/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.30/1.51    inference(flattening,[],[f18])).
% 7.30/1.51  
% 7.30/1.51  fof(f41,plain,(
% 7.30/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f19])).
% 7.30/1.51  
% 7.30/1.51  fof(f3,axiom,(
% 7.30/1.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 7.30/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.30/1.51  
% 7.30/1.51  fof(f12,plain,(
% 7.30/1.51    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.30/1.51    inference(ennf_transformation,[],[f3])).
% 7.30/1.51  
% 7.30/1.51  fof(f13,plain,(
% 7.30/1.51    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.30/1.51    inference(flattening,[],[f12])).
% 7.30/1.51  
% 7.30/1.51  fof(f42,plain,(
% 7.30/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.30/1.51    inference(cnf_transformation,[],[f13])).
% 7.30/1.51  
% 7.30/1.51  fof(f40,plain,(
% 7.30/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.30/1.51    inference(cnf_transformation,[],[f19])).
% 7.30/1.51  
% 7.30/1.51  fof(f58,plain,(
% 7.30/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.30/1.51    inference(equality_resolution,[],[f40])).
% 7.30/1.51  
% 7.30/1.51  fof(f47,plain,(
% 7.30/1.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.30/1.51    inference(cnf_transformation,[],[f27])).
% 7.30/1.51  
% 7.30/1.51  fof(f63,plain,(
% 7.30/1.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.30/1.51    inference(equality_resolution,[],[f47])).
% 7.30/1.51  
% 7.30/1.51  fof(f57,plain,(
% 7.30/1.51    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 7.30/1.51    inference(cnf_transformation,[],[f35])).
% 7.30/1.51  
% 7.30/1.51  fof(f56,plain,(
% 7.30/1.51    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 7.30/1.51    inference(cnf_transformation,[],[f35])).
% 7.30/1.51  
% 7.30/1.51  cnf(c_0,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_10063,plain,
% 7.30/1.51      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
% 7.30/1.51      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_xboole_0(X0,k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_23305,plain,
% 7.30/1.51      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_10063]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_5038,plain,
% 7.30/1.51      ( ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),X0)
% 7.30/1.51      | ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 7.30/1.51      | ~ r1_xboole_0(X0,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_5891,plain,
% 7.30/1.51      ( ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
% 7.30/1.51      | ~ r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 7.30/1.51      | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_5038]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_16,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.30/1.51      | r2_hidden(sK4(X0,X2,X1),X2)
% 7.30/1.51      | ~ v1_relat_1(X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_21,negated_conjecture,
% 7.30/1.51      ( v1_relat_1(sK6) ),
% 7.30/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_308,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.30/1.51      | r2_hidden(sK4(X0,X2,X1),X2)
% 7.30/1.51      | sK6 != X1 ),
% 7.30/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_309,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 7.30/1.51      | r2_hidden(sK4(X0,X1,sK6),X1) ),
% 7.30/1.51      inference(unflattening,[status(thm)],[c_308]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_4012,plain,
% 7.30/1.51      ( r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 7.30/1.51      | ~ r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_309]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_18,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.30/1.51      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 7.30/1.51      | ~ v1_relat_1(X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_284,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.30/1.51      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 7.30/1.51      | sK6 != X1 ),
% 7.30/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_285,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 7.30/1.51      | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
% 7.30/1.51      inference(unflattening,[status(thm)],[c_284]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_4014,plain,
% 7.30/1.51      ( r2_hidden(sK4(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
% 7.30/1.51      | ~ r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_285]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_15,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,X1)
% 7.30/1.51      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.30/1.51      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.30/1.51      | ~ v1_relat_1(X3) ),
% 7.30/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_264,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,X1)
% 7.30/1.51      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.30/1.51      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.30/1.51      | sK6 != X3 ),
% 7.30/1.51      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_265,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,X1)
% 7.30/1.51      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 7.30/1.51      | ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 7.30/1.51      inference(unflattening,[status(thm)],[c_264]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_13,plain,
% 7.30/1.51      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_277,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,X1)
% 7.30/1.51      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 7.30/1.51      inference(forward_subsumption_resolution,
% 7.30/1.51                [status(thm)],
% 7.30/1.51                [c_265,c_13]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1365,plain,
% 7.30/1.51      ( r2_hidden(X0,k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
% 7.30/1.51      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_277]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2509,plain,
% 7.30/1.51      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 7.30/1.51      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1365]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2,plain,
% 7.30/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1204,plain,
% 7.30/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.30/1.51      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.30/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_7,plain,
% 7.30/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.30/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_10,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 7.30/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1200,plain,
% 7.30/1.51      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.30/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2123,plain,
% 7.30/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.30/1.51      inference(superposition,[status(thm)],[c_7,c_1200]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2207,plain,
% 7.30/1.51      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.30/1.51      inference(superposition,[status(thm)],[c_1204,c_2123]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2238,plain,
% 7.30/1.51      ( r1_xboole_0(k1_xboole_0,X0) ),
% 7.30/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2207]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2240,plain,
% 7.30/1.51      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_2238]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_773,plain,
% 7.30/1.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.30/1.51      theory(equality) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2065,plain,
% 7.30/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.30/1.51      | r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | k10_relat_1(sK6,sK5) != X0
% 7.30/1.51      | k10_relat_1(sK6,sK5) != X1 ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_773]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2067,plain,
% 7.30/1.51      ( r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.30/1.51      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_2065]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1,plain,
% 7.30/1.51      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_2062,plain,
% 7.30/1.51      ( r2_hidden(sK0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5))
% 7.30/1.51      | r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_772,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1538,plain,
% 7.30/1.51      ( X0 != X1
% 7.30/1.51      | k10_relat_1(sK6,sK5) != X1
% 7.30/1.51      | k10_relat_1(sK6,sK5) = X0 ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_772]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1754,plain,
% 7.30/1.51      ( X0 != k10_relat_1(sK6,sK5)
% 7.30/1.51      | k10_relat_1(sK6,sK5) = X0
% 7.30/1.51      | k10_relat_1(sK6,sK5) != k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1538]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1756,plain,
% 7.30/1.51      ( k10_relat_1(sK6,sK5) != k10_relat_1(sK6,sK5)
% 7.30/1.51      | k10_relat_1(sK6,sK5) = k1_xboole_0
% 7.30/1.51      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1754]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_3,plain,
% 7.30/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.30/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1532,plain,
% 7.30/1.51      ( ~ r1_tarski(X0,k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
% 7.30/1.51      | k10_relat_1(sK6,sK5) = X0 ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1750,plain,
% 7.30/1.51      ( ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | k10_relat_1(sK6,sK5) = k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1532]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_6,plain,
% 7.30/1.51      ( ~ r1_tarski(X0,X1)
% 7.30/1.51      | ~ r1_tarski(X0,X2)
% 7.30/1.51      | ~ r1_xboole_0(X1,X2)
% 7.30/1.51      | k1_xboole_0 = X0 ),
% 7.30/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1468,plain,
% 7.30/1.51      ( ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
% 7.30/1.51      | ~ r1_tarski(k10_relat_1(sK6,sK5),X1)
% 7.30/1.51      | ~ r1_xboole_0(X0,X1)
% 7.30/1.51      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1565,plain,
% 7.30/1.51      ( ~ r1_tarski(k10_relat_1(sK6,sK5),X0)
% 7.30/1.51      | ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 7.30/1.51      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1468]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1711,plain,
% 7.30/1.51      ( ~ r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5))
% 7.30/1.51      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1565]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_4,plain,
% 7.30/1.51      ( r1_tarski(X0,X0) ),
% 7.30/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1566,plain,
% 7.30/1.51      ( r1_tarski(k10_relat_1(sK6,sK5),k10_relat_1(sK6,sK5)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_14,plain,
% 7.30/1.51      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.30/1.51      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 7.30/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1393,plain,
% 7.30/1.51      ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 7.30/1.51      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1340,plain,
% 7.30/1.51      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 7.30/1.51      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_1337,plain,
% 7.30/1.51      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 7.30/1.51      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 7.30/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_19,negated_conjecture,
% 7.30/1.51      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 7.30/1.51      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(c_20,negated_conjecture,
% 7.30/1.51      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 7.30/1.51      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 7.30/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.30/1.51  
% 7.30/1.51  cnf(contradiction,plain,
% 7.30/1.51      ( $false ),
% 7.30/1.51      inference(minisat,
% 7.30/1.51                [status(thm)],
% 7.30/1.51                [c_23305,c_5891,c_4012,c_4014,c_2509,c_2240,c_2067,
% 7.30/1.51                 c_2062,c_1756,c_1750,c_1711,c_1566,c_1393,c_1340,c_1337,
% 7.30/1.51                 c_19,c_20]) ).
% 7.30/1.51  
% 7.30/1.51  
% 7.30/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.30/1.51  
% 7.30/1.51  ------                               Statistics
% 7.30/1.51  
% 7.30/1.51  ------ General
% 7.30/1.51  
% 7.30/1.51  abstr_ref_over_cycles:                  0
% 7.30/1.51  abstr_ref_under_cycles:                 0
% 7.30/1.51  gc_basic_clause_elim:                   0
% 7.30/1.51  forced_gc_time:                         0
% 7.30/1.51  parsing_time:                           0.009
% 7.30/1.51  unif_index_cands_time:                  0.
% 7.30/1.51  unif_index_add_time:                    0.
% 7.30/1.51  orderings_time:                         0.
% 7.30/1.51  out_proof_time:                         0.009
% 7.30/1.51  total_time:                             0.607
% 7.30/1.51  num_of_symbols:                         47
% 7.30/1.51  num_of_terms:                           21159
% 7.30/1.51  
% 7.30/1.51  ------ Preprocessing
% 7.30/1.51  
% 7.30/1.51  num_of_splits:                          0
% 7.30/1.51  num_of_split_atoms:                     0
% 7.30/1.51  num_of_reused_defs:                     0
% 7.30/1.51  num_eq_ax_congr_red:                    37
% 7.30/1.51  num_of_sem_filtered_clauses:            1
% 7.30/1.51  num_of_subtypes:                        0
% 7.30/1.51  monotx_restored_types:                  0
% 7.30/1.51  sat_num_of_epr_types:                   0
% 7.30/1.51  sat_num_of_non_cyclic_types:            0
% 7.30/1.51  sat_guarded_non_collapsed_types:        0
% 7.30/1.51  num_pure_diseq_elim:                    0
% 7.30/1.51  simp_replaced_by:                       0
% 7.30/1.51  res_preprocessed:                       100
% 7.30/1.51  prep_upred:                             0
% 7.30/1.51  prep_unflattend:                        36
% 7.30/1.51  smt_new_axioms:                         0
% 7.30/1.51  pred_elim_cands:                        3
% 7.30/1.51  pred_elim:                              1
% 7.30/1.51  pred_elim_cl:                           1
% 7.30/1.51  pred_elim_cycles:                       3
% 7.30/1.51  merged_defs:                            8
% 7.30/1.51  merged_defs_ncl:                        0
% 7.30/1.51  bin_hyper_res:                          8
% 7.30/1.51  prep_cycles:                            4
% 7.30/1.51  pred_elim_time:                         0.005
% 7.30/1.51  splitting_time:                         0.
% 7.30/1.51  sem_filter_time:                        0.
% 7.30/1.51  monotx_time:                            0.
% 7.30/1.51  subtype_inf_time:                       0.
% 7.30/1.51  
% 7.30/1.51  ------ Problem properties
% 7.30/1.51  
% 7.30/1.51  clauses:                                20
% 7.30/1.51  conjectures:                            2
% 7.30/1.51  epr:                                    4
% 7.30/1.51  horn:                                   15
% 7.30/1.51  ground:                                 2
% 7.30/1.51  unary:                                  4
% 7.30/1.51  binary:                                 9
% 7.30/1.52  lits:                                   44
% 7.30/1.52  lits_eq:                                11
% 7.30/1.52  fd_pure:                                0
% 7.30/1.52  fd_pseudo:                              0
% 7.30/1.52  fd_cond:                                2
% 7.30/1.52  fd_pseudo_cond:                         3
% 7.30/1.52  ac_symbols:                             0
% 7.30/1.52  
% 7.30/1.52  ------ Propositional Solver
% 7.30/1.52  
% 7.30/1.52  prop_solver_calls:                      35
% 7.30/1.52  prop_fast_solver_calls:                 888
% 7.30/1.52  smt_solver_calls:                       0
% 7.30/1.52  smt_fast_solver_calls:                  0
% 7.30/1.52  prop_num_of_clauses:                    8723
% 7.30/1.52  prop_preprocess_simplified:             14043
% 7.30/1.52  prop_fo_subsumed:                       2
% 7.30/1.52  prop_solver_time:                       0.
% 7.30/1.52  smt_solver_time:                        0.
% 7.30/1.52  smt_fast_solver_time:                   0.
% 7.30/1.52  prop_fast_solver_time:                  0.
% 7.30/1.52  prop_unsat_core_time:                   0.001
% 7.30/1.52  
% 7.30/1.52  ------ QBF
% 7.30/1.52  
% 7.30/1.52  qbf_q_res:                              0
% 7.30/1.52  qbf_num_tautologies:                    0
% 7.30/1.52  qbf_prep_cycles:                        0
% 7.30/1.52  
% 7.30/1.52  ------ BMC1
% 7.30/1.52  
% 7.30/1.52  bmc1_current_bound:                     -1
% 7.30/1.52  bmc1_last_solved_bound:                 -1
% 7.30/1.52  bmc1_unsat_core_size:                   -1
% 7.30/1.52  bmc1_unsat_core_parents_size:           -1
% 7.30/1.52  bmc1_merge_next_fun:                    0
% 7.30/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.30/1.52  
% 7.30/1.52  ------ Instantiation
% 7.30/1.52  
% 7.30/1.52  inst_num_of_clauses:                    2425
% 7.30/1.52  inst_num_in_passive:                    1050
% 7.30/1.52  inst_num_in_active:                     1075
% 7.30/1.52  inst_num_in_unprocessed:                299
% 7.30/1.52  inst_num_of_loops:                      1301
% 7.30/1.52  inst_num_of_learning_restarts:          0
% 7.30/1.52  inst_num_moves_active_passive:          218
% 7.30/1.52  inst_lit_activity:                      0
% 7.30/1.52  inst_lit_activity_moves:                0
% 7.30/1.52  inst_num_tautologies:                   0
% 7.30/1.52  inst_num_prop_implied:                  0
% 7.30/1.52  inst_num_existing_simplified:           0
% 7.30/1.52  inst_num_eq_res_simplified:             0
% 7.30/1.52  inst_num_child_elim:                    0
% 7.30/1.52  inst_num_of_dismatching_blockings:      961
% 7.30/1.52  inst_num_of_non_proper_insts:           2784
% 7.30/1.52  inst_num_of_duplicates:                 0
% 7.30/1.52  inst_inst_num_from_inst_to_res:         0
% 7.30/1.52  inst_dismatching_checking_time:         0.
% 7.30/1.52  
% 7.30/1.52  ------ Resolution
% 7.30/1.52  
% 7.30/1.52  res_num_of_clauses:                     0
% 7.30/1.52  res_num_in_passive:                     0
% 7.30/1.52  res_num_in_active:                      0
% 7.30/1.52  res_num_of_loops:                       104
% 7.30/1.52  res_forward_subset_subsumed:            114
% 7.30/1.52  res_backward_subset_subsumed:           2
% 7.30/1.52  res_forward_subsumed:                   0
% 7.30/1.52  res_backward_subsumed:                  0
% 7.30/1.52  res_forward_subsumption_resolution:     1
% 7.30/1.52  res_backward_subsumption_resolution:    0
% 7.30/1.52  res_clause_to_clause_subsumption:       3236
% 7.30/1.52  res_orphan_elimination:                 0
% 7.30/1.52  res_tautology_del:                      277
% 7.30/1.52  res_num_eq_res_simplified:              0
% 7.30/1.52  res_num_sel_changes:                    0
% 7.30/1.52  res_moves_from_active_to_pass:          0
% 7.30/1.52  
% 7.30/1.52  ------ Superposition
% 7.30/1.52  
% 7.30/1.52  sup_time_total:                         0.
% 7.30/1.52  sup_time_generating:                    0.
% 7.30/1.52  sup_time_sim_full:                      0.
% 7.30/1.52  sup_time_sim_immed:                     0.
% 7.30/1.52  
% 7.30/1.52  sup_num_of_clauses:                     891
% 7.30/1.52  sup_num_in_active:                      148
% 7.30/1.52  sup_num_in_passive:                     743
% 7.30/1.52  sup_num_of_loops:                       260
% 7.30/1.52  sup_fw_superposition:                   1047
% 7.30/1.52  sup_bw_superposition:                   308
% 7.30/1.52  sup_immediate_simplified:               297
% 7.30/1.52  sup_given_eliminated:                   3
% 7.30/1.52  comparisons_done:                       0
% 7.30/1.52  comparisons_avoided:                    0
% 7.30/1.52  
% 7.30/1.52  ------ Simplifications
% 7.30/1.52  
% 7.30/1.52  
% 7.30/1.52  sim_fw_subset_subsumed:                 123
% 7.30/1.52  sim_bw_subset_subsumed:                 0
% 7.30/1.52  sim_fw_subsumed:                        34
% 7.30/1.52  sim_bw_subsumed:                        15
% 7.30/1.52  sim_fw_subsumption_res:                 0
% 7.30/1.52  sim_bw_subsumption_res:                 0
% 7.30/1.52  sim_tautology_del:                      3
% 7.30/1.52  sim_eq_tautology_del:                   56
% 7.30/1.52  sim_eq_res_simp:                        0
% 7.30/1.52  sim_fw_demodulated:                     0
% 7.30/1.52  sim_bw_demodulated:                     481
% 7.30/1.52  sim_light_normalised:                   131
% 7.30/1.52  sim_joinable_taut:                      0
% 7.30/1.52  sim_joinable_simp:                      0
% 7.30/1.52  sim_ac_normalised:                      0
% 7.30/1.52  sim_smt_subsumption:                    0
% 7.30/1.52  
%------------------------------------------------------------------------------
