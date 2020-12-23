%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0549+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:33 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 186 expanded)
%              Number of clauses        :   53 (  60 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  346 ( 727 expanded)
%              Number of equality atoms :   64 ( 144 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k9_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) = k1_xboole_0 )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
        | k9_relat_1(sK8,sK7) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(sK8),sK7)
        | k9_relat_1(sK8,sK7) = k1_xboole_0 )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
      | k9_relat_1(sK8,sK7) != k1_xboole_0 )
    & ( r1_xboole_0(k1_relat_1(sK8),sK7)
      | k9_relat_1(sK8,sK7) = k1_xboole_0 )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f42,f43])).

fof(f69,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f33])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK8),sK7)
    | k9_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2214,plain,
    ( ~ r1_xboole_0(X0,sK7)
    | ~ r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),X0)
    | ~ r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10986,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | ~ r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),k1_relat_1(sK8))
    | ~ r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_872,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9351,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_9353,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9351])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4745,plain,
    ( ~ r2_hidden(sK2(sK8,sK6(k1_relat_1(sK8),sK7)),k9_relat_1(sK8,sK7))
    | ~ v1_xboole_0(k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_399,c_3])).

cnf(c_1993,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,sK7))
    | ~ r2_hidden(sK6(k1_relat_1(sK8),sK7),sK7)
    | ~ r2_hidden(k4_tarski(sK6(k1_relat_1(sK8),sK7),X0),sK8) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_2609,plain,
    ( ~ r2_hidden(sK6(k1_relat_1(sK8),sK7),sK7)
    | r2_hidden(sK2(sK8,sK6(k1_relat_1(sK8),sK7)),k9_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(sK6(k1_relat_1(sK8),sK7),sK2(sK8,sK6(k1_relat_1(sK8),sK7))),sK8) ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1964,plain,
    ( ~ r2_hidden(sK6(k1_relat_1(sK8),sK7),k1_relat_1(sK8))
    | r2_hidden(k4_tarski(sK6(k1_relat_1(sK8),sK7),sK2(sK8,sK6(k1_relat_1(sK8),sK7))),sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK5(X0,X1,sK8),X1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1764,plain,
    ( r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),sK7)
    | ~ r2_hidden(sK4(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k1_relat_1(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK5(X0,X1,sK8),k1_relat_1(sK8)) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1766,plain,
    ( r2_hidden(sK5(sK4(k9_relat_1(sK8,sK7)),sK7,sK8),k1_relat_1(sK8))
    | ~ r2_hidden(sK4(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_12,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_340,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK4(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_341,plain,
    ( r2_hidden(sK4(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_1672,plain,
    ( r2_hidden(sK4(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7))
    | v1_xboole_0(k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1667,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k9_relat_1(sK8,sK7))
    | k9_relat_1(sK8,sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_1669,plain,
    ( v1_xboole_0(k9_relat_1(sK8,sK7))
    | ~ v1_xboole_0(k1_xboole_0)
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1624,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK8,sK7))
    | k1_xboole_0 = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_866,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1618,plain,
    ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_867,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1601,plain,
    ( k9_relat_1(sK8,sK7) != X0
    | k9_relat_1(sK8,sK7) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_1617,plain,
    ( k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7)
    | k9_relat_1(sK8,sK7) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK6(X0,X1),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_196,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_504,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | k9_relat_1(sK8,sK7) != k1_xboole_0
    | k1_relat_1(sK8) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_196])).

cnf(c_505,plain,
    ( r2_hidden(sK6(k1_relat_1(sK8),sK7),sK7)
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_21,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK6(X0,X1),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_494,plain,
    ( r2_hidden(sK6(X0,X1),X0)
    | k9_relat_1(sK8,sK7) != k1_xboole_0
    | k1_relat_1(sK8) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_196])).

cnf(c_495,plain,
    ( r2_hidden(sK6(k1_relat_1(sK8),sK7),k1_relat_1(sK8))
    | k9_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_375,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_376,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK8),sK7)
    | k9_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10986,c_9353,c_4745,c_2609,c_1964,c_1764,c_1766,c_1672,c_1669,c_1624,c_1618,c_1617,c_505,c_495,c_376,c_11,c_25])).


%------------------------------------------------------------------------------
