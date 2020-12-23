%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:33 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 243 expanded)
%              Number of clauses        :   71 (  89 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 ( 924 expanded)
%              Number of equality atoms :  113 ( 236 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
        | k1_xboole_0 != k9_relat_1(sK7,sK6) )
      & ( r1_xboole_0(k1_relat_1(sK7),sK6)
        | k1_xboole_0 = k9_relat_1(sK7,sK6) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
      | k1_xboole_0 != k9_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k1_relat_1(sK7),sK6)
      | k1_xboole_0 = k9_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f36])).

fof(f56,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 = k9_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f26])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 != k9_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_794,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4672,plain,
    ( sK2(sK7,sK5(k1_relat_1(sK7),sK6)) = sK2(sK7,sK5(k1_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_798,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2881,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6))
    | X1 != k9_relat_1(sK7,sK6)
    | X0 != sK2(sK7,sK5(k1_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_4671,plain,
    ( r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),X0)
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6))
    | X0 != k9_relat_1(sK7,sK6)
    | sK2(sK7,sK5(k1_relat_1(sK7),sK6)) != sK2(sK7,sK5(k1_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_4674,plain,
    ( ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6))
    | r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k1_xboole_0)
    | sK2(sK7,sK5(k1_relat_1(sK7),sK6)) != sK2(sK7,sK5(k1_relat_1(sK7),sK6))
    | k1_xboole_0 != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_4671])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2876,plain,
    ( ~ r1_xboole_0(X0,k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),X0)
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2878,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 = k9_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1202,plain,
    ( k1_xboole_0 = k9_relat_1(sK7,sK6)
    | r1_xboole_0(k1_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1207,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1566,plain,
    ( k9_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(sK7),sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1202,c_1207])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1208,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1668,plain,
    ( k9_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_1208])).

cnf(c_1206,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2251,plain,
    ( k9_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1206])).

cnf(c_6,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_271,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_272,plain,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_286,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_272,c_16])).

cnf(c_1393,plain,
    ( r2_hidden(sK3(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
    | k1_xboole_0 = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK4(X0,X1,sK7),k1_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1415,plain,
    ( r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),k1_relat_1(sK7))
    | ~ r2_hidden(sK3(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_345,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK4(X0,X1,sK7),X1) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1413,plain,
    ( r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),sK6)
    | ~ r2_hidden(sK3(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1669,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k9_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1668])).

cnf(c_795,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1423,plain,
    ( X0 != X1
    | k9_relat_1(sK7,sK6) != X1
    | k9_relat_1(sK7,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1726,plain,
    ( X0 != k9_relat_1(sK7,sK6)
    | k9_relat_1(sK7,sK6) = X0
    | k9_relat_1(sK7,sK6) != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_1728,plain,
    ( k9_relat_1(sK7,sK6) != k9_relat_1(sK7,sK6)
    | k9_relat_1(sK7,sK6) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_1727,plain,
    ( k9_relat_1(sK7,sK6) = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1732,plain,
    ( ~ r1_xboole_0(X0,sK6)
    | ~ r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),X0)
    | ~ r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2172,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | ~ r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),k1_relat_1(sK7))
    | ~ r2_hidden(sK4(sK3(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_2357,plain,
    ( k9_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2251,c_1393,c_1415,c_1413,c_1669,c_1728,c_1727,c_2172])).

cnf(c_799,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1813,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k9_relat_1(sK7,sK6))
    | X2 != X0
    | k9_relat_1(sK7,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_1815,plain,
    ( r1_xboole_0(k1_xboole_0,k9_relat_1(sK7,sK6))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k9_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_301,c_2])).

cnf(c_1353,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK5(k1_relat_1(sK7),sK6),sK6)
    | ~ r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6),X0),sK7) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1533,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6),sK6)
    | r2_hidden(sK2(sK7,sK5(k1_relat_1(sK7),sK6)),k9_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6),sK2(sK7,sK5(k1_relat_1(sK7),sK6))),sK7) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1396,plain,
    ( k9_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1397,plain,
    ( k9_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1362,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6),k1_relat_1(sK7))
    | r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6),sK2(sK7,sK5(k1_relat_1(sK7),sK6))),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_809,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 != k9_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_157,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 != k9_relat_1(sK7,sK6) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_439,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | k9_relat_1(sK7,sK6) != k1_xboole_0
    | k1_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_157])).

cnf(c_440,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK6),sK6)
    | k9_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_429,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k9_relat_1(sK7,sK6) != k1_xboole_0
    | k1_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_157])).

cnf(c_430,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK6),k1_relat_1(sK7))
    | k9_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_54,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_48,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4672,c_4674,c_2878,c_2357,c_1815,c_1533,c_1397,c_1362,c_809,c_440,c_430,c_54,c_48])).


%------------------------------------------------------------------------------
