%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:57 EST 2020

% Result     : Theorem 55.25s
% Output     : CNFRefutation 55.25s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 581 expanded)
%              Number of clauses        :   66 (  83 expanded)
%              Number of leaves         :   26 ( 170 expanded)
%              Depth                    :   16
%              Number of atoms          :  402 (1134 expanded)
%              Number of equality atoms :  161 ( 630 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f81])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f72,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2 )
   => ( ( k1_tarski(sK8) != k2_relat_1(sK9)
        | k1_tarski(sK7) != k1_relat_1(sK9) )
      & k1_tarski(k4_tarski(sK7,sK8)) = sK9 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k1_tarski(sK8) != k2_relat_1(sK9)
      | k1_tarski(sK7) != k1_relat_1(sK9) )
    & k1_tarski(k4_tarski(sK7,sK8)) = sK9 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f23,f44])).

fof(f75,plain,(
    k1_tarski(k4_tarski(sK7,sK8)) = sK9 ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f89,plain,(
    k6_enumset1(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)) = sK9 ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f63,f81,f81,f82])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f64,f81])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f76,plain,
    ( k1_tarski(sK8) != k2_relat_1(sK9)
    | k1_tarski(sK7) != k1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,
    ( k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k2_relat_1(sK9)
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k1_relat_1(sK9) ),
    inference(definition_unfolding,[],[f76,f82,f82])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_140229,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK9))
    | ~ r2_hidden(sK8,k2_relat_1(sK9))
    | r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,X0),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_211233,plain,
    ( ~ r2_hidden(sK8,k2_relat_1(sK9))
    | r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_140229])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_77500,plain,
    ( ~ r2_hidden(k4_tarski(sK7,X0),sK9)
    | r2_hidden(sK7,k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_105381,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
    | r2_hidden(sK7,k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_77500])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_105378,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
    | r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_753,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_741,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)) = sK9 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1294,plain,
    ( k2_zfmisc_1(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_23,c_9])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_748,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1383,plain,
    ( r2_hidden(X0,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_748])).

cnf(c_1943,plain,
    ( r2_hidden(X0,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_1383])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_754,plain,
    ( r2_hidden(sK0(X0,X1),X0) != iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2984,plain,
    ( r2_hidden(sK0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),X0),k1_relat_1(sK9)) != iProver_top
    | r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1943,c_754])).

cnf(c_89350,plain,
    ( r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_2984])).

cnf(c_89351,plain,
    ( ~ r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_89350])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6509,plain,
    ( r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_751,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_745,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2080,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_745])).

cnf(c_3530,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK7,sK8),X0),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK9,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_2080])).

cnf(c_3580,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)),X0) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK9,sK9),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_3530])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_749,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3591,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),X0) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_749])).

cnf(c_3932,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_3591])).

cnf(c_3934,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3932])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1748,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK9))
    | r2_xboole_0(X0,k2_relat_1(sK9))
    | k2_relat_1(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2415,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_relat_1(sK9))
    | r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_relat_1(sK9))
    | k2_relat_1(sK9) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_3902,plain,
    ( ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9))
    | r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9))
    | k2_relat_1(sK9) = k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1908,plain,
    ( ~ r1_tarski(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0)
    | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3397,plain,
    ( ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_429,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1238,plain,
    ( k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != X0
    | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k2_relat_1(sK9)
    | k2_relat_1(sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_1918,plain,
    ( k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)
    | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k2_relat_1(sK9)
    | k2_relat_1(sK9) != k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_737,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1382,plain,
    ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_749])).

cnf(c_1506,plain,
    ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_1382])).

cnf(c_1626,plain,
    ( r2_hidden(sK0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0),k2_relat_1(sK9)) != iProver_top
    | r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_754])).

cnf(c_1835,plain,
    ( r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_1626])).

cnf(c_1836,plain,
    ( ~ r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1835])).

cnf(c_799,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK9))
    | r2_xboole_0(X0,k1_relat_1(sK9))
    | k1_relat_1(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_976,plain,
    ( ~ r1_tarski(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9))
    | r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9))
    | k1_relat_1(sK9) = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_781,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X0
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK9)
    | k1_relat_1(sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_902,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK9)
    | k1_relat_1(sK9) != k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_783,plain,
    ( ~ r2_hidden(sK7,k1_relat_1(sK9))
    | r1_tarski(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_434,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_441,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_68,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_64,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k1_relat_1(sK9)
    | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k2_relat_1(sK9) ),
    inference(cnf_transformation,[],[f88])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_211233,c_105381,c_105378,c_89351,c_6509,c_3934,c_3902,c_3397,c_1918,c_1836,c_976,c_902,c_783,c_441,c_68,c_64,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.25/7.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.25/7.51  
% 55.25/7.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.25/7.51  
% 55.25/7.51  ------  iProver source info
% 55.25/7.51  
% 55.25/7.51  git: date: 2020-06-30 10:37:57 +0100
% 55.25/7.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.25/7.51  git: non_committed_changes: false
% 55.25/7.51  git: last_make_outside_of_git: false
% 55.25/7.51  
% 55.25/7.51  ------ 
% 55.25/7.51  
% 55.25/7.51  ------ Input Options
% 55.25/7.51  
% 55.25/7.51  --out_options                           all
% 55.25/7.51  --tptp_safe_out                         true
% 55.25/7.51  --problem_path                          ""
% 55.25/7.51  --include_path                          ""
% 55.25/7.51  --clausifier                            res/vclausify_rel
% 55.25/7.51  --clausifier_options                    ""
% 55.25/7.51  --stdin                                 false
% 55.25/7.51  --stats_out                             all
% 55.25/7.51  
% 55.25/7.51  ------ General Options
% 55.25/7.51  
% 55.25/7.51  --fof                                   false
% 55.25/7.51  --time_out_real                         305.
% 55.25/7.51  --time_out_virtual                      -1.
% 55.25/7.51  --symbol_type_check                     false
% 55.25/7.51  --clausify_out                          false
% 55.25/7.51  --sig_cnt_out                           false
% 55.25/7.51  --trig_cnt_out                          false
% 55.25/7.51  --trig_cnt_out_tolerance                1.
% 55.25/7.51  --trig_cnt_out_sk_spl                   false
% 55.25/7.51  --abstr_cl_out                          false
% 55.25/7.51  
% 55.25/7.51  ------ Global Options
% 55.25/7.51  
% 55.25/7.51  --schedule                              default
% 55.25/7.51  --add_important_lit                     false
% 55.25/7.51  --prop_solver_per_cl                    1000
% 55.25/7.51  --min_unsat_core                        false
% 55.25/7.51  --soft_assumptions                      false
% 55.25/7.51  --soft_lemma_size                       3
% 55.25/7.51  --prop_impl_unit_size                   0
% 55.25/7.51  --prop_impl_unit                        []
% 55.25/7.51  --share_sel_clauses                     true
% 55.25/7.51  --reset_solvers                         false
% 55.25/7.51  --bc_imp_inh                            [conj_cone]
% 55.25/7.51  --conj_cone_tolerance                   3.
% 55.25/7.51  --extra_neg_conj                        none
% 55.25/7.51  --large_theory_mode                     true
% 55.25/7.51  --prolific_symb_bound                   200
% 55.25/7.51  --lt_threshold                          2000
% 55.25/7.51  --clause_weak_htbl                      true
% 55.25/7.51  --gc_record_bc_elim                     false
% 55.25/7.51  
% 55.25/7.51  ------ Preprocessing Options
% 55.25/7.51  
% 55.25/7.51  --preprocessing_flag                    true
% 55.25/7.51  --time_out_prep_mult                    0.1
% 55.25/7.51  --splitting_mode                        input
% 55.25/7.51  --splitting_grd                         true
% 55.25/7.51  --splitting_cvd                         false
% 55.25/7.51  --splitting_cvd_svl                     false
% 55.25/7.51  --splitting_nvd                         32
% 55.25/7.51  --sub_typing                            true
% 55.25/7.51  --prep_gs_sim                           true
% 55.25/7.51  --prep_unflatten                        true
% 55.25/7.51  --prep_res_sim                          true
% 55.25/7.51  --prep_upred                            true
% 55.25/7.51  --prep_sem_filter                       exhaustive
% 55.25/7.51  --prep_sem_filter_out                   false
% 55.25/7.51  --pred_elim                             true
% 55.25/7.51  --res_sim_input                         true
% 55.25/7.51  --eq_ax_congr_red                       true
% 55.25/7.51  --pure_diseq_elim                       true
% 55.25/7.51  --brand_transform                       false
% 55.25/7.51  --non_eq_to_eq                          false
% 55.25/7.51  --prep_def_merge                        true
% 55.25/7.51  --prep_def_merge_prop_impl              false
% 55.25/7.51  --prep_def_merge_mbd                    true
% 55.25/7.51  --prep_def_merge_tr_red                 false
% 55.25/7.51  --prep_def_merge_tr_cl                  false
% 55.25/7.51  --smt_preprocessing                     true
% 55.25/7.51  --smt_ac_axioms                         fast
% 55.25/7.51  --preprocessed_out                      false
% 55.25/7.51  --preprocessed_stats                    false
% 55.25/7.51  
% 55.25/7.51  ------ Abstraction refinement Options
% 55.25/7.51  
% 55.25/7.51  --abstr_ref                             []
% 55.25/7.51  --abstr_ref_prep                        false
% 55.25/7.51  --abstr_ref_until_sat                   false
% 55.25/7.51  --abstr_ref_sig_restrict                funpre
% 55.25/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.25/7.51  --abstr_ref_under                       []
% 55.25/7.51  
% 55.25/7.51  ------ SAT Options
% 55.25/7.51  
% 55.25/7.51  --sat_mode                              false
% 55.25/7.51  --sat_fm_restart_options                ""
% 55.25/7.51  --sat_gr_def                            false
% 55.25/7.51  --sat_epr_types                         true
% 55.25/7.51  --sat_non_cyclic_types                  false
% 55.25/7.51  --sat_finite_models                     false
% 55.25/7.51  --sat_fm_lemmas                         false
% 55.25/7.51  --sat_fm_prep                           false
% 55.25/7.51  --sat_fm_uc_incr                        true
% 55.25/7.51  --sat_out_model                         small
% 55.25/7.51  --sat_out_clauses                       false
% 55.25/7.51  
% 55.25/7.51  ------ QBF Options
% 55.25/7.51  
% 55.25/7.51  --qbf_mode                              false
% 55.25/7.51  --qbf_elim_univ                         false
% 55.25/7.51  --qbf_dom_inst                          none
% 55.25/7.51  --qbf_dom_pre_inst                      false
% 55.25/7.51  --qbf_sk_in                             false
% 55.25/7.51  --qbf_pred_elim                         true
% 55.25/7.51  --qbf_split                             512
% 55.25/7.51  
% 55.25/7.51  ------ BMC1 Options
% 55.25/7.51  
% 55.25/7.51  --bmc1_incremental                      false
% 55.25/7.51  --bmc1_axioms                           reachable_all
% 55.25/7.51  --bmc1_min_bound                        0
% 55.25/7.51  --bmc1_max_bound                        -1
% 55.25/7.51  --bmc1_max_bound_default                -1
% 55.25/7.51  --bmc1_symbol_reachability              true
% 55.25/7.51  --bmc1_property_lemmas                  false
% 55.25/7.51  --bmc1_k_induction                      false
% 55.25/7.51  --bmc1_non_equiv_states                 false
% 55.25/7.51  --bmc1_deadlock                         false
% 55.25/7.51  --bmc1_ucm                              false
% 55.25/7.51  --bmc1_add_unsat_core                   none
% 55.25/7.51  --bmc1_unsat_core_children              false
% 55.25/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.25/7.51  --bmc1_out_stat                         full
% 55.25/7.51  --bmc1_ground_init                      false
% 55.25/7.51  --bmc1_pre_inst_next_state              false
% 55.25/7.51  --bmc1_pre_inst_state                   false
% 55.25/7.51  --bmc1_pre_inst_reach_state             false
% 55.25/7.51  --bmc1_out_unsat_core                   false
% 55.25/7.51  --bmc1_aig_witness_out                  false
% 55.25/7.51  --bmc1_verbose                          false
% 55.25/7.51  --bmc1_dump_clauses_tptp                false
% 55.25/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.25/7.51  --bmc1_dump_file                        -
% 55.25/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.25/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.25/7.51  --bmc1_ucm_extend_mode                  1
% 55.25/7.51  --bmc1_ucm_init_mode                    2
% 55.25/7.51  --bmc1_ucm_cone_mode                    none
% 55.25/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.25/7.51  --bmc1_ucm_relax_model                  4
% 55.25/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.25/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.25/7.51  --bmc1_ucm_layered_model                none
% 55.25/7.51  --bmc1_ucm_max_lemma_size               10
% 55.25/7.51  
% 55.25/7.51  ------ AIG Options
% 55.25/7.51  
% 55.25/7.51  --aig_mode                              false
% 55.25/7.51  
% 55.25/7.51  ------ Instantiation Options
% 55.25/7.51  
% 55.25/7.51  --instantiation_flag                    true
% 55.25/7.51  --inst_sos_flag                         true
% 55.25/7.51  --inst_sos_phase                        true
% 55.25/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.25/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.25/7.51  --inst_lit_sel_side                     num_symb
% 55.25/7.51  --inst_solver_per_active                1400
% 55.25/7.51  --inst_solver_calls_frac                1.
% 55.25/7.51  --inst_passive_queue_type               priority_queues
% 55.25/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.25/7.51  --inst_passive_queues_freq              [25;2]
% 55.25/7.51  --inst_dismatching                      true
% 55.25/7.51  --inst_eager_unprocessed_to_passive     true
% 55.25/7.51  --inst_prop_sim_given                   true
% 55.25/7.51  --inst_prop_sim_new                     false
% 55.25/7.51  --inst_subs_new                         false
% 55.25/7.51  --inst_eq_res_simp                      false
% 55.25/7.51  --inst_subs_given                       false
% 55.25/7.51  --inst_orphan_elimination               true
% 55.25/7.51  --inst_learning_loop_flag               true
% 55.25/7.51  --inst_learning_start                   3000
% 55.25/7.51  --inst_learning_factor                  2
% 55.25/7.51  --inst_start_prop_sim_after_learn       3
% 55.25/7.51  --inst_sel_renew                        solver
% 55.25/7.51  --inst_lit_activity_flag                true
% 55.25/7.51  --inst_restr_to_given                   false
% 55.25/7.51  --inst_activity_threshold               500
% 55.25/7.51  --inst_out_proof                        true
% 55.25/7.51  
% 55.25/7.51  ------ Resolution Options
% 55.25/7.51  
% 55.25/7.51  --resolution_flag                       true
% 55.25/7.51  --res_lit_sel                           adaptive
% 55.25/7.51  --res_lit_sel_side                      none
% 55.25/7.51  --res_ordering                          kbo
% 55.25/7.51  --res_to_prop_solver                    active
% 55.25/7.51  --res_prop_simpl_new                    false
% 55.25/7.51  --res_prop_simpl_given                  true
% 55.25/7.51  --res_passive_queue_type                priority_queues
% 55.25/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.25/7.51  --res_passive_queues_freq               [15;5]
% 55.25/7.51  --res_forward_subs                      full
% 55.25/7.51  --res_backward_subs                     full
% 55.25/7.51  --res_forward_subs_resolution           true
% 55.25/7.51  --res_backward_subs_resolution          true
% 55.25/7.51  --res_orphan_elimination                true
% 55.25/7.51  --res_time_limit                        2.
% 55.25/7.51  --res_out_proof                         true
% 55.25/7.51  
% 55.25/7.51  ------ Superposition Options
% 55.25/7.51  
% 55.25/7.51  --superposition_flag                    true
% 55.25/7.51  --sup_passive_queue_type                priority_queues
% 55.25/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.25/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.25/7.51  --demod_completeness_check              fast
% 55.25/7.51  --demod_use_ground                      true
% 55.25/7.51  --sup_to_prop_solver                    passive
% 55.25/7.51  --sup_prop_simpl_new                    true
% 55.25/7.51  --sup_prop_simpl_given                  true
% 55.25/7.51  --sup_fun_splitting                     true
% 55.25/7.51  --sup_smt_interval                      50000
% 55.25/7.51  
% 55.25/7.51  ------ Superposition Simplification Setup
% 55.25/7.51  
% 55.25/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.25/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.25/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.25/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.25/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.25/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.25/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.25/7.51  --sup_immed_triv                        [TrivRules]
% 55.25/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_immed_bw_main                     []
% 55.25/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.25/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.25/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_input_bw                          []
% 55.25/7.51  
% 55.25/7.51  ------ Combination Options
% 55.25/7.51  
% 55.25/7.51  --comb_res_mult                         3
% 55.25/7.51  --comb_sup_mult                         2
% 55.25/7.51  --comb_inst_mult                        10
% 55.25/7.51  
% 55.25/7.51  ------ Debug Options
% 55.25/7.51  
% 55.25/7.51  --dbg_backtrace                         false
% 55.25/7.51  --dbg_dump_prop_clauses                 false
% 55.25/7.51  --dbg_dump_prop_clauses_file            -
% 55.25/7.51  --dbg_out_stat                          false
% 55.25/7.51  ------ Parsing...
% 55.25/7.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.25/7.51  
% 55.25/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.25/7.51  
% 55.25/7.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.25/7.51  
% 55.25/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.25/7.51  ------ Proving...
% 55.25/7.51  ------ Problem Properties 
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  clauses                                 23
% 55.25/7.51  conjectures                             2
% 55.25/7.51  EPR                                     3
% 55.25/7.51  Horn                                    20
% 55.25/7.51  unary                                   4
% 55.25/7.51  binary                                  11
% 55.25/7.51  lits                                    50
% 55.25/7.51  lits eq                                 11
% 55.25/7.51  fd_pure                                 0
% 55.25/7.51  fd_pseudo                               0
% 55.25/7.51  fd_cond                                 0
% 55.25/7.51  fd_pseudo_cond                          6
% 55.25/7.51  AC symbols                              0
% 55.25/7.51  
% 55.25/7.51  ------ Schedule dynamic 5 is on 
% 55.25/7.51  
% 55.25/7.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  ------ 
% 55.25/7.51  Current options:
% 55.25/7.51  ------ 
% 55.25/7.51  
% 55.25/7.51  ------ Input Options
% 55.25/7.51  
% 55.25/7.51  --out_options                           all
% 55.25/7.51  --tptp_safe_out                         true
% 55.25/7.51  --problem_path                          ""
% 55.25/7.51  --include_path                          ""
% 55.25/7.51  --clausifier                            res/vclausify_rel
% 55.25/7.51  --clausifier_options                    ""
% 55.25/7.51  --stdin                                 false
% 55.25/7.51  --stats_out                             all
% 55.25/7.51  
% 55.25/7.51  ------ General Options
% 55.25/7.51  
% 55.25/7.51  --fof                                   false
% 55.25/7.51  --time_out_real                         305.
% 55.25/7.51  --time_out_virtual                      -1.
% 55.25/7.51  --symbol_type_check                     false
% 55.25/7.51  --clausify_out                          false
% 55.25/7.51  --sig_cnt_out                           false
% 55.25/7.51  --trig_cnt_out                          false
% 55.25/7.51  --trig_cnt_out_tolerance                1.
% 55.25/7.51  --trig_cnt_out_sk_spl                   false
% 55.25/7.51  --abstr_cl_out                          false
% 55.25/7.51  
% 55.25/7.51  ------ Global Options
% 55.25/7.51  
% 55.25/7.51  --schedule                              default
% 55.25/7.51  --add_important_lit                     false
% 55.25/7.51  --prop_solver_per_cl                    1000
% 55.25/7.51  --min_unsat_core                        false
% 55.25/7.51  --soft_assumptions                      false
% 55.25/7.51  --soft_lemma_size                       3
% 55.25/7.51  --prop_impl_unit_size                   0
% 55.25/7.51  --prop_impl_unit                        []
% 55.25/7.51  --share_sel_clauses                     true
% 55.25/7.51  --reset_solvers                         false
% 55.25/7.51  --bc_imp_inh                            [conj_cone]
% 55.25/7.51  --conj_cone_tolerance                   3.
% 55.25/7.51  --extra_neg_conj                        none
% 55.25/7.51  --large_theory_mode                     true
% 55.25/7.51  --prolific_symb_bound                   200
% 55.25/7.51  --lt_threshold                          2000
% 55.25/7.51  --clause_weak_htbl                      true
% 55.25/7.51  --gc_record_bc_elim                     false
% 55.25/7.51  
% 55.25/7.51  ------ Preprocessing Options
% 55.25/7.51  
% 55.25/7.51  --preprocessing_flag                    true
% 55.25/7.51  --time_out_prep_mult                    0.1
% 55.25/7.51  --splitting_mode                        input
% 55.25/7.51  --splitting_grd                         true
% 55.25/7.51  --splitting_cvd                         false
% 55.25/7.51  --splitting_cvd_svl                     false
% 55.25/7.51  --splitting_nvd                         32
% 55.25/7.51  --sub_typing                            true
% 55.25/7.51  --prep_gs_sim                           true
% 55.25/7.51  --prep_unflatten                        true
% 55.25/7.51  --prep_res_sim                          true
% 55.25/7.51  --prep_upred                            true
% 55.25/7.51  --prep_sem_filter                       exhaustive
% 55.25/7.51  --prep_sem_filter_out                   false
% 55.25/7.51  --pred_elim                             true
% 55.25/7.51  --res_sim_input                         true
% 55.25/7.51  --eq_ax_congr_red                       true
% 55.25/7.51  --pure_diseq_elim                       true
% 55.25/7.51  --brand_transform                       false
% 55.25/7.51  --non_eq_to_eq                          false
% 55.25/7.51  --prep_def_merge                        true
% 55.25/7.51  --prep_def_merge_prop_impl              false
% 55.25/7.51  --prep_def_merge_mbd                    true
% 55.25/7.51  --prep_def_merge_tr_red                 false
% 55.25/7.51  --prep_def_merge_tr_cl                  false
% 55.25/7.51  --smt_preprocessing                     true
% 55.25/7.51  --smt_ac_axioms                         fast
% 55.25/7.51  --preprocessed_out                      false
% 55.25/7.51  --preprocessed_stats                    false
% 55.25/7.51  
% 55.25/7.51  ------ Abstraction refinement Options
% 55.25/7.51  
% 55.25/7.51  --abstr_ref                             []
% 55.25/7.51  --abstr_ref_prep                        false
% 55.25/7.51  --abstr_ref_until_sat                   false
% 55.25/7.51  --abstr_ref_sig_restrict                funpre
% 55.25/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.25/7.51  --abstr_ref_under                       []
% 55.25/7.51  
% 55.25/7.51  ------ SAT Options
% 55.25/7.51  
% 55.25/7.51  --sat_mode                              false
% 55.25/7.51  --sat_fm_restart_options                ""
% 55.25/7.51  --sat_gr_def                            false
% 55.25/7.51  --sat_epr_types                         true
% 55.25/7.51  --sat_non_cyclic_types                  false
% 55.25/7.51  --sat_finite_models                     false
% 55.25/7.51  --sat_fm_lemmas                         false
% 55.25/7.51  --sat_fm_prep                           false
% 55.25/7.51  --sat_fm_uc_incr                        true
% 55.25/7.51  --sat_out_model                         small
% 55.25/7.51  --sat_out_clauses                       false
% 55.25/7.51  
% 55.25/7.51  ------ QBF Options
% 55.25/7.51  
% 55.25/7.51  --qbf_mode                              false
% 55.25/7.51  --qbf_elim_univ                         false
% 55.25/7.51  --qbf_dom_inst                          none
% 55.25/7.51  --qbf_dom_pre_inst                      false
% 55.25/7.51  --qbf_sk_in                             false
% 55.25/7.51  --qbf_pred_elim                         true
% 55.25/7.51  --qbf_split                             512
% 55.25/7.51  
% 55.25/7.51  ------ BMC1 Options
% 55.25/7.51  
% 55.25/7.51  --bmc1_incremental                      false
% 55.25/7.51  --bmc1_axioms                           reachable_all
% 55.25/7.51  --bmc1_min_bound                        0
% 55.25/7.51  --bmc1_max_bound                        -1
% 55.25/7.51  --bmc1_max_bound_default                -1
% 55.25/7.51  --bmc1_symbol_reachability              true
% 55.25/7.51  --bmc1_property_lemmas                  false
% 55.25/7.51  --bmc1_k_induction                      false
% 55.25/7.51  --bmc1_non_equiv_states                 false
% 55.25/7.51  --bmc1_deadlock                         false
% 55.25/7.51  --bmc1_ucm                              false
% 55.25/7.51  --bmc1_add_unsat_core                   none
% 55.25/7.51  --bmc1_unsat_core_children              false
% 55.25/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.25/7.51  --bmc1_out_stat                         full
% 55.25/7.51  --bmc1_ground_init                      false
% 55.25/7.51  --bmc1_pre_inst_next_state              false
% 55.25/7.51  --bmc1_pre_inst_state                   false
% 55.25/7.51  --bmc1_pre_inst_reach_state             false
% 55.25/7.51  --bmc1_out_unsat_core                   false
% 55.25/7.51  --bmc1_aig_witness_out                  false
% 55.25/7.51  --bmc1_verbose                          false
% 55.25/7.51  --bmc1_dump_clauses_tptp                false
% 55.25/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.25/7.51  --bmc1_dump_file                        -
% 55.25/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.25/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.25/7.51  --bmc1_ucm_extend_mode                  1
% 55.25/7.51  --bmc1_ucm_init_mode                    2
% 55.25/7.51  --bmc1_ucm_cone_mode                    none
% 55.25/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.25/7.51  --bmc1_ucm_relax_model                  4
% 55.25/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.25/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.25/7.51  --bmc1_ucm_layered_model                none
% 55.25/7.51  --bmc1_ucm_max_lemma_size               10
% 55.25/7.51  
% 55.25/7.51  ------ AIG Options
% 55.25/7.51  
% 55.25/7.51  --aig_mode                              false
% 55.25/7.51  
% 55.25/7.51  ------ Instantiation Options
% 55.25/7.51  
% 55.25/7.51  --instantiation_flag                    true
% 55.25/7.51  --inst_sos_flag                         true
% 55.25/7.51  --inst_sos_phase                        true
% 55.25/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.25/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.25/7.51  --inst_lit_sel_side                     none
% 55.25/7.51  --inst_solver_per_active                1400
% 55.25/7.51  --inst_solver_calls_frac                1.
% 55.25/7.51  --inst_passive_queue_type               priority_queues
% 55.25/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.25/7.51  --inst_passive_queues_freq              [25;2]
% 55.25/7.51  --inst_dismatching                      true
% 55.25/7.51  --inst_eager_unprocessed_to_passive     true
% 55.25/7.51  --inst_prop_sim_given                   true
% 55.25/7.51  --inst_prop_sim_new                     false
% 55.25/7.51  --inst_subs_new                         false
% 55.25/7.51  --inst_eq_res_simp                      false
% 55.25/7.51  --inst_subs_given                       false
% 55.25/7.51  --inst_orphan_elimination               true
% 55.25/7.51  --inst_learning_loop_flag               true
% 55.25/7.51  --inst_learning_start                   3000
% 55.25/7.51  --inst_learning_factor                  2
% 55.25/7.51  --inst_start_prop_sim_after_learn       3
% 55.25/7.51  --inst_sel_renew                        solver
% 55.25/7.51  --inst_lit_activity_flag                true
% 55.25/7.51  --inst_restr_to_given                   false
% 55.25/7.51  --inst_activity_threshold               500
% 55.25/7.51  --inst_out_proof                        true
% 55.25/7.51  
% 55.25/7.51  ------ Resolution Options
% 55.25/7.51  
% 55.25/7.51  --resolution_flag                       false
% 55.25/7.51  --res_lit_sel                           adaptive
% 55.25/7.51  --res_lit_sel_side                      none
% 55.25/7.51  --res_ordering                          kbo
% 55.25/7.51  --res_to_prop_solver                    active
% 55.25/7.51  --res_prop_simpl_new                    false
% 55.25/7.51  --res_prop_simpl_given                  true
% 55.25/7.51  --res_passive_queue_type                priority_queues
% 55.25/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.25/7.51  --res_passive_queues_freq               [15;5]
% 55.25/7.51  --res_forward_subs                      full
% 55.25/7.51  --res_backward_subs                     full
% 55.25/7.51  --res_forward_subs_resolution           true
% 55.25/7.51  --res_backward_subs_resolution          true
% 55.25/7.51  --res_orphan_elimination                true
% 55.25/7.51  --res_time_limit                        2.
% 55.25/7.51  --res_out_proof                         true
% 55.25/7.51  
% 55.25/7.51  ------ Superposition Options
% 55.25/7.51  
% 55.25/7.51  --superposition_flag                    true
% 55.25/7.51  --sup_passive_queue_type                priority_queues
% 55.25/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.25/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.25/7.51  --demod_completeness_check              fast
% 55.25/7.51  --demod_use_ground                      true
% 55.25/7.51  --sup_to_prop_solver                    passive
% 55.25/7.51  --sup_prop_simpl_new                    true
% 55.25/7.51  --sup_prop_simpl_given                  true
% 55.25/7.51  --sup_fun_splitting                     true
% 55.25/7.51  --sup_smt_interval                      50000
% 55.25/7.51  
% 55.25/7.51  ------ Superposition Simplification Setup
% 55.25/7.51  
% 55.25/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.25/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.25/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.25/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.25/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.25/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.25/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.25/7.51  --sup_immed_triv                        [TrivRules]
% 55.25/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_immed_bw_main                     []
% 55.25/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.25/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.25/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.25/7.51  --sup_input_bw                          []
% 55.25/7.51  
% 55.25/7.51  ------ Combination Options
% 55.25/7.51  
% 55.25/7.51  --comb_res_mult                         3
% 55.25/7.51  --comb_sup_mult                         2
% 55.25/7.51  --comb_inst_mult                        10
% 55.25/7.51  
% 55.25/7.51  ------ Debug Options
% 55.25/7.51  
% 55.25/7.51  --dbg_backtrace                         false
% 55.25/7.51  --dbg_dump_prop_clauses                 false
% 55.25/7.51  --dbg_dump_prop_clauses_file            -
% 55.25/7.51  --dbg_out_stat                          false
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  ------ Proving...
% 55.25/7.51  
% 55.25/7.51  
% 55.25/7.51  % SZS status Theorem for theBenchmark.p
% 55.25/7.51  
% 55.25/7.51  % SZS output start CNFRefutation for theBenchmark.p
% 55.25/7.51  
% 55.25/7.51  fof(f13,axiom,(
% 55.25/7.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f30,plain,(
% 55.25/7.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 55.25/7.51    inference(nnf_transformation,[],[f13])).
% 55.25/7.51  
% 55.25/7.51  fof(f31,plain,(
% 55.25/7.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 55.25/7.51    inference(flattening,[],[f30])).
% 55.25/7.51  
% 55.25/7.51  fof(f66,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f31])).
% 55.25/7.51  
% 55.25/7.51  fof(f5,axiom,(
% 55.25/7.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f53,plain,(
% 55.25/7.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f5])).
% 55.25/7.51  
% 55.25/7.51  fof(f6,axiom,(
% 55.25/7.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f54,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f6])).
% 55.25/7.51  
% 55.25/7.51  fof(f7,axiom,(
% 55.25/7.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f55,plain,(
% 55.25/7.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f7])).
% 55.25/7.51  
% 55.25/7.51  fof(f8,axiom,(
% 55.25/7.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f56,plain,(
% 55.25/7.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f8])).
% 55.25/7.51  
% 55.25/7.51  fof(f9,axiom,(
% 55.25/7.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f57,plain,(
% 55.25/7.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f9])).
% 55.25/7.51  
% 55.25/7.51  fof(f10,axiom,(
% 55.25/7.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f58,plain,(
% 55.25/7.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f10])).
% 55.25/7.51  
% 55.25/7.51  fof(f77,plain,(
% 55.25/7.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f57,f58])).
% 55.25/7.51  
% 55.25/7.51  fof(f78,plain,(
% 55.25/7.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f56,f77])).
% 55.25/7.51  
% 55.25/7.51  fof(f79,plain,(
% 55.25/7.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f55,f78])).
% 55.25/7.51  
% 55.25/7.51  fof(f80,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f54,f79])).
% 55.25/7.51  
% 55.25/7.51  fof(f81,plain,(
% 55.25/7.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f53,f80])).
% 55.25/7.51  
% 55.25/7.51  fof(f85,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f66,f81])).
% 55.25/7.51  
% 55.25/7.51  fof(f14,axiom,(
% 55.25/7.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f32,plain,(
% 55.25/7.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 55.25/7.51    inference(nnf_transformation,[],[f14])).
% 55.25/7.51  
% 55.25/7.51  fof(f33,plain,(
% 55.25/7.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 55.25/7.51    inference(rectify,[],[f32])).
% 55.25/7.51  
% 55.25/7.51  fof(f36,plain,(
% 55.25/7.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f35,plain,(
% 55.25/7.51    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f34,plain,(
% 55.25/7.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f37,plain,(
% 55.25/7.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 55.25/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 55.25/7.51  
% 55.25/7.51  fof(f68,plain,(
% 55.25/7.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 55.25/7.51    inference(cnf_transformation,[],[f37])).
% 55.25/7.51  
% 55.25/7.51  fof(f92,plain,(
% 55.25/7.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 55.25/7.51    inference(equality_resolution,[],[f68])).
% 55.25/7.51  
% 55.25/7.51  fof(f15,axiom,(
% 55.25/7.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f38,plain,(
% 55.25/7.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 55.25/7.51    inference(nnf_transformation,[],[f15])).
% 55.25/7.51  
% 55.25/7.51  fof(f39,plain,(
% 55.25/7.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.25/7.51    inference(rectify,[],[f38])).
% 55.25/7.51  
% 55.25/7.51  fof(f42,plain,(
% 55.25/7.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f41,plain,(
% 55.25/7.51    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f40,plain,(
% 55.25/7.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f43,plain,(
% 55.25/7.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.25/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 55.25/7.51  
% 55.25/7.51  fof(f72,plain,(
% 55.25/7.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 55.25/7.51    inference(cnf_transformation,[],[f43])).
% 55.25/7.51  
% 55.25/7.51  fof(f94,plain,(
% 55.25/7.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 55.25/7.51    inference(equality_resolution,[],[f72])).
% 55.25/7.51  
% 55.25/7.51  fof(f2,axiom,(
% 55.25/7.51    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f22,plain,(
% 55.25/7.51    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 55.25/7.51    inference(ennf_transformation,[],[f2])).
% 55.25/7.51  
% 55.25/7.51  fof(f24,plain,(
% 55.25/7.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1)))),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f25,plain,(
% 55.25/7.51    ! [X0,X1] : ((~r2_hidden(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 55.25/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f24])).
% 55.25/7.51  
% 55.25/7.51  fof(f47,plain,(
% 55.25/7.51    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f25])).
% 55.25/7.51  
% 55.25/7.51  fof(f67,plain,(
% 55.25/7.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 55.25/7.51    inference(cnf_transformation,[],[f37])).
% 55.25/7.51  
% 55.25/7.51  fof(f93,plain,(
% 55.25/7.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 55.25/7.51    inference(equality_resolution,[],[f67])).
% 55.25/7.51  
% 55.25/7.51  fof(f16,conjecture,(
% 55.25/7.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f17,negated_conjecture,(
% 55.25/7.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 55.25/7.51    inference(negated_conjecture,[],[f16])).
% 55.25/7.51  
% 55.25/7.51  fof(f19,plain,(
% 55.25/7.51    ~! [X0,X1,X2] : (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)))),
% 55.25/7.51    inference(pure_predicate_removal,[],[f17])).
% 55.25/7.51  
% 55.25/7.51  fof(f23,plain,(
% 55.25/7.51    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2)),
% 55.25/7.51    inference(ennf_transformation,[],[f19])).
% 55.25/7.51  
% 55.25/7.51  fof(f44,plain,(
% 55.25/7.51    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) => ((k1_tarski(sK8) != k2_relat_1(sK9) | k1_tarski(sK7) != k1_relat_1(sK9)) & k1_tarski(k4_tarski(sK7,sK8)) = sK9)),
% 55.25/7.51    introduced(choice_axiom,[])).
% 55.25/7.51  
% 55.25/7.51  fof(f45,plain,(
% 55.25/7.51    (k1_tarski(sK8) != k2_relat_1(sK9) | k1_tarski(sK7) != k1_relat_1(sK9)) & k1_tarski(k4_tarski(sK7,sK8)) = sK9),
% 55.25/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f23,f44])).
% 55.25/7.51  
% 55.25/7.51  fof(f75,plain,(
% 55.25/7.51    k1_tarski(k4_tarski(sK7,sK8)) = sK9),
% 55.25/7.51    inference(cnf_transformation,[],[f45])).
% 55.25/7.51  
% 55.25/7.51  fof(f4,axiom,(
% 55.25/7.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f52,plain,(
% 55.25/7.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f4])).
% 55.25/7.51  
% 55.25/7.51  fof(f82,plain,(
% 55.25/7.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f52,f81])).
% 55.25/7.51  
% 55.25/7.51  fof(f89,plain,(
% 55.25/7.51    k6_enumset1(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)) = sK9),
% 55.25/7.51    inference(definition_unfolding,[],[f75,f82])).
% 55.25/7.51  
% 55.25/7.51  fof(f12,axiom,(
% 55.25/7.51    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f63,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 55.25/7.51    inference(cnf_transformation,[],[f12])).
% 55.25/7.51  
% 55.25/7.51  fof(f83,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 55.25/7.51    inference(definition_unfolding,[],[f63,f81,f81,f82])).
% 55.25/7.51  
% 55.25/7.51  fof(f11,axiom,(
% 55.25/7.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f28,plain,(
% 55.25/7.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 55.25/7.51    inference(nnf_transformation,[],[f11])).
% 55.25/7.51  
% 55.25/7.51  fof(f29,plain,(
% 55.25/7.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 55.25/7.51    inference(flattening,[],[f28])).
% 55.25/7.51  
% 55.25/7.51  fof(f59,plain,(
% 55.25/7.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 55.25/7.51    inference(cnf_transformation,[],[f29])).
% 55.25/7.51  
% 55.25/7.51  fof(f48,plain,(
% 55.25/7.51    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f25])).
% 55.25/7.51  
% 55.25/7.51  fof(f3,axiom,(
% 55.25/7.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f26,plain,(
% 55.25/7.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.25/7.51    inference(nnf_transformation,[],[f3])).
% 55.25/7.51  
% 55.25/7.51  fof(f27,plain,(
% 55.25/7.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.25/7.51    inference(flattening,[],[f26])).
% 55.25/7.51  
% 55.25/7.51  fof(f50,plain,(
% 55.25/7.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 55.25/7.51    inference(cnf_transformation,[],[f27])).
% 55.25/7.51  
% 55.25/7.51  fof(f90,plain,(
% 55.25/7.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.25/7.51    inference(equality_resolution,[],[f50])).
% 55.25/7.51  
% 55.25/7.51  fof(f64,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f31])).
% 55.25/7.51  
% 55.25/7.51  fof(f87,plain,(
% 55.25/7.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 55.25/7.51    inference(definition_unfolding,[],[f64,f81])).
% 55.25/7.51  
% 55.25/7.51  fof(f60,plain,(
% 55.25/7.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 55.25/7.51    inference(cnf_transformation,[],[f29])).
% 55.25/7.51  
% 55.25/7.51  fof(f1,axiom,(
% 55.25/7.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 55.25/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.25/7.51  
% 55.25/7.51  fof(f18,plain,(
% 55.25/7.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 55.25/7.51    inference(unused_predicate_definition_removal,[],[f1])).
% 55.25/7.51  
% 55.25/7.51  fof(f20,plain,(
% 55.25/7.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 55.25/7.51    inference(ennf_transformation,[],[f18])).
% 55.25/7.51  
% 55.25/7.51  fof(f21,plain,(
% 55.25/7.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 55.25/7.51    inference(flattening,[],[f20])).
% 55.25/7.51  
% 55.25/7.51  fof(f46,plain,(
% 55.25/7.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f21])).
% 55.25/7.51  
% 55.25/7.51  fof(f51,plain,(
% 55.25/7.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 55.25/7.51    inference(cnf_transformation,[],[f27])).
% 55.25/7.51  
% 55.25/7.51  fof(f71,plain,(
% 55.25/7.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 55.25/7.52    inference(cnf_transformation,[],[f43])).
% 55.25/7.52  
% 55.25/7.52  fof(f95,plain,(
% 55.25/7.52    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 55.25/7.52    inference(equality_resolution,[],[f71])).
% 55.25/7.52  
% 55.25/7.52  fof(f49,plain,(
% 55.25/7.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.25/7.52    inference(cnf_transformation,[],[f27])).
% 55.25/7.52  
% 55.25/7.52  fof(f91,plain,(
% 55.25/7.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.25/7.52    inference(equality_resolution,[],[f49])).
% 55.25/7.52  
% 55.25/7.52  fof(f76,plain,(
% 55.25/7.52    k1_tarski(sK8) != k2_relat_1(sK9) | k1_tarski(sK7) != k1_relat_1(sK9)),
% 55.25/7.52    inference(cnf_transformation,[],[f45])).
% 55.25/7.52  
% 55.25/7.52  fof(f88,plain,(
% 55.25/7.52    k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k2_relat_1(sK9) | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k1_relat_1(sK9)),
% 55.25/7.52    inference(definition_unfolding,[],[f76,f82,f82])).
% 55.25/7.52  
% 55.25/7.52  cnf(c_11,plain,
% 55.25/7.52      ( ~ r2_hidden(X0,X1)
% 55.25/7.52      | ~ r2_hidden(X2,X1)
% 55.25/7.52      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f85]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_140229,plain,
% 55.25/7.52      ( ~ r2_hidden(X0,k2_relat_1(sK9))
% 55.25/7.52      | ~ r2_hidden(sK8,k2_relat_1(sK9))
% 55.25/7.52      | r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,X0),k2_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_11]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_211233,plain,
% 55.25/7.52      ( ~ r2_hidden(sK8,k2_relat_1(sK9))
% 55.25/7.52      | r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_140229]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_16,plain,
% 55.25/7.52      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f92]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_77500,plain,
% 55.25/7.52      ( ~ r2_hidden(k4_tarski(sK7,X0),sK9)
% 55.25/7.52      | r2_hidden(sK7,k1_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_16]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_105381,plain,
% 55.25/7.52      ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
% 55.25/7.52      | r2_hidden(sK7,k1_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_77500]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_20,plain,
% 55.25/7.52      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f94]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_105378,plain,
% 55.25/7.52      ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
% 55.25/7.52      | r2_hidden(sK8,k2_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_20]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_2,plain,
% 55.25/7.52      ( r2_hidden(sK0(X0,X1),X1) | ~ r2_xboole_0(X0,X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f47]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_753,plain,
% 55.25/7.52      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 55.25/7.52      | r2_xboole_0(X0,X1) != iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_17,plain,
% 55.25/7.52      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 55.25/7.52      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f93]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_741,plain,
% 55.25/7.52      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_23,negated_conjecture,
% 55.25/7.52      ( k6_enumset1(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)) = sK9 ),
% 55.25/7.52      inference(cnf_transformation,[],[f89]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_9,plain,
% 55.25/7.52      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 55.25/7.52      inference(cnf_transformation,[],[f83]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1294,plain,
% 55.25/7.52      ( k2_zfmisc_1(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = sK9 ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_23,c_9]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_8,plain,
% 55.25/7.52      ( r2_hidden(X0,X1)
% 55.25/7.52      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 55.25/7.52      inference(cnf_transformation,[],[f59]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_748,plain,
% 55.25/7.52      ( r2_hidden(X0,X1) = iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1383,plain,
% 55.25/7.52      ( r2_hidden(X0,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_1294,c_748]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1943,plain,
% 55.25/7.52      ( r2_hidden(X0,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top
% 55.25/7.52      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_741,c_1383]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1,plain,
% 55.25/7.52      ( ~ r2_hidden(sK0(X0,X1),X0) | ~ r2_xboole_0(X0,X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f48]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_754,plain,
% 55.25/7.52      ( r2_hidden(sK0(X0,X1),X0) != iProver_top
% 55.25/7.52      | r2_xboole_0(X0,X1) != iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_2984,plain,
% 55.25/7.52      ( r2_hidden(sK0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),X0),k1_relat_1(sK9)) != iProver_top
% 55.25/7.52      | r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),X0) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_1943,c_754]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_89350,plain,
% 55.25/7.52      ( r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_753,c_2984]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_89351,plain,
% 55.25/7.52      ( ~ r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) ),
% 55.25/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_89350]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_4,plain,
% 55.25/7.52      ( r1_tarski(X0,X0) ),
% 55.25/7.52      inference(cnf_transformation,[],[f90]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_6509,plain,
% 55.25/7.52      ( r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_4]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_751,plain,
% 55.25/7.52      ( r1_tarski(X0,X0) = iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_13,plain,
% 55.25/7.52      ( r2_hidden(X0,X1)
% 55.25/7.52      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f87]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_745,plain,
% 55.25/7.52      ( r2_hidden(X0,X1) = iProver_top
% 55.25/7.52      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_2080,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 55.25/7.52      | r1_tarski(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),X2) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_9,c_745]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3530,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(k4_tarski(sK7,sK8),X0),X1) = iProver_top
% 55.25/7.52      | r1_tarski(k2_zfmisc_1(sK9,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X1) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_23,c_2080]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3580,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(k4_tarski(sK7,sK8),k4_tarski(sK7,sK8)),X0) = iProver_top
% 55.25/7.52      | r1_tarski(k2_zfmisc_1(sK9,sK9),X0) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_23,c_3530]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_7,plain,
% 55.25/7.52      ( r2_hidden(X0,X1)
% 55.25/7.52      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 55.25/7.52      inference(cnf_transformation,[],[f60]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_749,plain,
% 55.25/7.52      ( r2_hidden(X0,X1) = iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3591,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(sK7,sK8),X0) = iProver_top
% 55.25/7.52      | r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(X1,X0)) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_3580,c_749]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3932,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(sK7,sK8),sK9) = iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_751,c_3591]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3934,plain,
% 55.25/7.52      ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
% 55.25/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_3932]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_0,plain,
% 55.25/7.52      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 55.25/7.52      inference(cnf_transformation,[],[f46]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1748,plain,
% 55.25/7.52      ( ~ r1_tarski(X0,k2_relat_1(sK9))
% 55.25/7.52      | r2_xboole_0(X0,k2_relat_1(sK9))
% 55.25/7.52      | k2_relat_1(sK9) = X0 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_0]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_2415,plain,
% 55.25/7.52      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_relat_1(sK9))
% 55.25/7.52      | r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_relat_1(sK9))
% 55.25/7.52      | k2_relat_1(sK9) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_1748]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3902,plain,
% 55.25/7.52      ( ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9))
% 55.25/7.52      | r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9))
% 55.25/7.52      | k2_relat_1(sK9) = k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_2415]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3,plain,
% 55.25/7.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 55.25/7.52      inference(cnf_transformation,[],[f51]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1908,plain,
% 55.25/7.52      ( ~ r1_tarski(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 55.25/7.52      | ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0)
% 55.25/7.52      | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = X0 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_3]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_3397,plain,
% 55.25/7.52      ( ~ r1_tarski(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 55.25/7.52      | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_1908]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_429,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1238,plain,
% 55.25/7.52      ( k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != X0
% 55.25/7.52      | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k2_relat_1(sK9)
% 55.25/7.52      | k2_relat_1(sK9) != X0 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_429]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1918,plain,
% 55.25/7.52      ( k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)
% 55.25/7.52      | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) = k2_relat_1(sK9)
% 55.25/7.52      | k2_relat_1(sK9) != k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_1238]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_21,plain,
% 55.25/7.52      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 55.25/7.52      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 55.25/7.52      inference(cnf_transformation,[],[f95]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_737,plain,
% 55.25/7.52      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 55.25/7.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1382,plain,
% 55.25/7.52      ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top
% 55.25/7.52      | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_1294,c_749]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1506,plain,
% 55.25/7.52      ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top
% 55.25/7.52      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_737,c_1382]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1626,plain,
% 55.25/7.52      ( r2_hidden(sK0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0),k2_relat_1(sK9)) != iProver_top
% 55.25/7.52      | r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),X0) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_1506,c_754]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1835,plain,
% 55.25/7.52      ( r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) != iProver_top ),
% 55.25/7.52      inference(superposition,[status(thm)],[c_753,c_1626]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_1836,plain,
% 55.25/7.52      ( ~ r2_xboole_0(k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8),k2_relat_1(sK9)) ),
% 55.25/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_1835]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_799,plain,
% 55.25/7.52      ( ~ r1_tarski(X0,k1_relat_1(sK9))
% 55.25/7.52      | r2_xboole_0(X0,k1_relat_1(sK9))
% 55.25/7.52      | k1_relat_1(sK9) = X0 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_0]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_976,plain,
% 55.25/7.52      ( ~ r1_tarski(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9))
% 55.25/7.52      | r2_xboole_0(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9))
% 55.25/7.52      | k1_relat_1(sK9) = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_799]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_781,plain,
% 55.25/7.52      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X0
% 55.25/7.52      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK9)
% 55.25/7.52      | k1_relat_1(sK9) != X0 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_429]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_902,plain,
% 55.25/7.52      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
% 55.25/7.52      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK9)
% 55.25/7.52      | k1_relat_1(sK9) != k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_781]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_783,plain,
% 55.25/7.52      ( ~ r2_hidden(sK7,k1_relat_1(sK9))
% 55.25/7.52      | r1_tarski(k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7),k1_relat_1(sK9)) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_11]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_434,plain,
% 55.25/7.52      ( X0 != X1
% 55.25/7.52      | X2 != X3
% 55.25/7.52      | X4 != X5
% 55.25/7.52      | X6 != X7
% 55.25/7.52      | X8 != X9
% 55.25/7.52      | X10 != X11
% 55.25/7.52      | X12 != X13
% 55.25/7.52      | X14 != X15
% 55.25/7.52      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 55.25/7.52      theory(equality) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_441,plain,
% 55.25/7.52      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
% 55.25/7.52      | sK7 != sK7 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_434]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_68,plain,
% 55.25/7.52      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_3]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_5,plain,
% 55.25/7.52      ( r1_tarski(X0,X0) ),
% 55.25/7.52      inference(cnf_transformation,[],[f91]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_64,plain,
% 55.25/7.52      ( r1_tarski(sK7,sK7) ),
% 55.25/7.52      inference(instantiation,[status(thm)],[c_5]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(c_22,negated_conjecture,
% 55.25/7.52      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != k1_relat_1(sK9)
% 55.25/7.52      | k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8) != k2_relat_1(sK9) ),
% 55.25/7.52      inference(cnf_transformation,[],[f88]) ).
% 55.25/7.52  
% 55.25/7.52  cnf(contradiction,plain,
% 55.25/7.52      ( $false ),
% 55.25/7.52      inference(minisat,
% 55.25/7.52                [status(thm)],
% 55.25/7.52                [c_211233,c_105381,c_105378,c_89351,c_6509,c_3934,c_3902,
% 55.25/7.52                 c_3397,c_1918,c_1836,c_976,c_902,c_783,c_441,c_68,c_64,
% 55.25/7.52                 c_22]) ).
% 55.25/7.52  
% 55.25/7.52  
% 55.25/7.52  % SZS output end CNFRefutation for theBenchmark.p
% 55.25/7.52  
% 55.25/7.52  ------                               Statistics
% 55.25/7.52  
% 55.25/7.52  ------ General
% 55.25/7.52  
% 55.25/7.52  abstr_ref_over_cycles:                  0
% 55.25/7.52  abstr_ref_under_cycles:                 0
% 55.25/7.52  gc_basic_clause_elim:                   0
% 55.25/7.52  forced_gc_time:                         0
% 55.25/7.52  parsing_time:                           0.016
% 55.25/7.52  unif_index_cands_time:                  0.
% 55.25/7.52  unif_index_add_time:                    0.
% 55.25/7.52  orderings_time:                         0.
% 55.25/7.52  out_proof_time:                         0.017
% 55.25/7.52  total_time:                             6.899
% 55.25/7.52  num_of_symbols:                         49
% 55.25/7.52  num_of_terms:                           258377
% 55.25/7.52  
% 55.25/7.52  ------ Preprocessing
% 55.25/7.52  
% 55.25/7.52  num_of_splits:                          0
% 55.25/7.52  num_of_split_atoms:                     0
% 55.25/7.52  num_of_reused_defs:                     0
% 55.25/7.52  num_eq_ax_congr_red:                    51
% 55.25/7.52  num_of_sem_filtered_clauses:            1
% 55.25/7.52  num_of_subtypes:                        0
% 55.25/7.52  monotx_restored_types:                  0
% 55.25/7.52  sat_num_of_epr_types:                   0
% 55.25/7.52  sat_num_of_non_cyclic_types:            0
% 55.25/7.52  sat_guarded_non_collapsed_types:        0
% 55.25/7.52  num_pure_diseq_elim:                    0
% 55.25/7.52  simp_replaced_by:                       0
% 55.25/7.52  res_preprocessed:                       111
% 55.25/7.52  prep_upred:                             0
% 55.25/7.52  prep_unflattend:                        0
% 55.25/7.52  smt_new_axioms:                         0
% 55.25/7.52  pred_elim_cands:                        3
% 55.25/7.52  pred_elim:                              0
% 55.25/7.52  pred_elim_cl:                           0
% 55.25/7.52  pred_elim_cycles:                       2
% 55.25/7.52  merged_defs:                            0
% 55.25/7.52  merged_defs_ncl:                        0
% 55.25/7.52  bin_hyper_res:                          0
% 55.25/7.52  prep_cycles:                            4
% 55.25/7.52  pred_elim_time:                         0.001
% 55.25/7.52  splitting_time:                         0.
% 55.25/7.52  sem_filter_time:                        0.
% 55.25/7.52  monotx_time:                            0.001
% 55.25/7.52  subtype_inf_time:                       0.
% 55.25/7.52  
% 55.25/7.52  ------ Problem properties
% 55.25/7.52  
% 55.25/7.52  clauses:                                23
% 55.25/7.52  conjectures:                            2
% 55.25/7.52  epr:                                    3
% 55.25/7.52  horn:                                   20
% 55.25/7.52  ground:                                 2
% 55.25/7.52  unary:                                  4
% 55.25/7.52  binary:                                 11
% 55.25/7.52  lits:                                   50
% 55.25/7.52  lits_eq:                                11
% 55.25/7.52  fd_pure:                                0
% 55.25/7.52  fd_pseudo:                              0
% 55.25/7.52  fd_cond:                                0
% 55.25/7.52  fd_pseudo_cond:                         6
% 55.25/7.52  ac_symbols:                             0
% 55.25/7.52  
% 55.25/7.52  ------ Propositional Solver
% 55.25/7.52  
% 55.25/7.52  prop_solver_calls:                      81
% 55.25/7.52  prop_fast_solver_calls:                 2690
% 55.25/7.52  smt_solver_calls:                       0
% 55.25/7.52  smt_fast_solver_calls:                  0
% 55.25/7.52  prop_num_of_clauses:                    80519
% 55.25/7.52  prop_preprocess_simplified:             140060
% 55.25/7.52  prop_fo_subsumed:                       1
% 55.25/7.52  prop_solver_time:                       0.
% 55.25/7.52  smt_solver_time:                        0.
% 55.25/7.52  smt_fast_solver_time:                   0.
% 55.25/7.52  prop_fast_solver_time:                  0.
% 55.25/7.52  prop_unsat_core_time:                   0.005
% 55.25/7.52  
% 55.25/7.52  ------ QBF
% 55.25/7.52  
% 55.25/7.52  qbf_q_res:                              0
% 55.25/7.52  qbf_num_tautologies:                    0
% 55.25/7.52  qbf_prep_cycles:                        0
% 55.25/7.52  
% 55.25/7.52  ------ BMC1
% 55.25/7.52  
% 55.25/7.52  bmc1_current_bound:                     -1
% 55.25/7.52  bmc1_last_solved_bound:                 -1
% 55.25/7.52  bmc1_unsat_core_size:                   -1
% 55.25/7.52  bmc1_unsat_core_parents_size:           -1
% 55.25/7.52  bmc1_merge_next_fun:                    0
% 55.25/7.52  bmc1_unsat_core_clauses_time:           0.
% 55.25/7.52  
% 55.25/7.52  ------ Instantiation
% 55.25/7.52  
% 55.25/7.52  inst_num_of_clauses:                    10676
% 55.25/7.52  inst_num_in_passive:                    6565
% 55.25/7.52  inst_num_in_active:                     4645
% 55.25/7.52  inst_num_in_unprocessed:                1577
% 55.25/7.52  inst_num_of_loops:                      7420
% 55.25/7.52  inst_num_of_learning_restarts:          1
% 55.25/7.52  inst_num_moves_active_passive:          2771
% 55.25/7.52  inst_lit_activity:                      0
% 55.25/7.52  inst_lit_activity_moves:                3
% 55.25/7.52  inst_num_tautologies:                   0
% 55.25/7.52  inst_num_prop_implied:                  0
% 55.25/7.52  inst_num_existing_simplified:           0
% 55.25/7.52  inst_num_eq_res_simplified:             0
% 55.25/7.52  inst_num_child_elim:                    0
% 55.25/7.52  inst_num_of_dismatching_blockings:      34691
% 55.25/7.52  inst_num_of_non_proper_insts:           25109
% 55.25/7.52  inst_num_of_duplicates:                 0
% 55.25/7.52  inst_inst_num_from_inst_to_res:         0
% 55.25/7.52  inst_dismatching_checking_time:         0.
% 55.25/7.52  
% 55.25/7.52  ------ Resolution
% 55.25/7.52  
% 55.25/7.52  res_num_of_clauses:                     32
% 55.25/7.52  res_num_in_passive:                     32
% 55.25/7.52  res_num_in_active:                      0
% 55.25/7.52  res_num_of_loops:                       115
% 55.25/7.52  res_forward_subset_subsumed:            338
% 55.25/7.52  res_backward_subset_subsumed:           2
% 55.25/7.52  res_forward_subsumed:                   0
% 55.25/7.52  res_backward_subsumed:                  0
% 55.25/7.52  res_forward_subsumption_resolution:     0
% 55.25/7.52  res_backward_subsumption_resolution:    0
% 55.25/7.52  res_clause_to_clause_subsumption:       31024
% 55.25/7.52  res_orphan_elimination:                 0
% 55.25/7.52  res_tautology_del:                      2133
% 55.25/7.52  res_num_eq_res_simplified:              0
% 55.25/7.52  res_num_sel_changes:                    0
% 55.25/7.52  res_moves_from_active_to_pass:          0
% 55.25/7.52  
% 55.25/7.52  ------ Superposition
% 55.25/7.52  
% 55.25/7.52  sup_time_total:                         0.
% 55.25/7.52  sup_time_generating:                    0.
% 55.25/7.52  sup_time_sim_full:                      0.
% 55.25/7.52  sup_time_sim_immed:                     0.
% 55.25/7.52  
% 55.25/7.52  sup_num_of_clauses:                     7928
% 55.25/7.52  sup_num_in_active:                      1256
% 55.25/7.52  sup_num_in_passive:                     6672
% 55.25/7.52  sup_num_of_loops:                       1484
% 55.25/7.52  sup_fw_superposition:                   5229
% 55.25/7.52  sup_bw_superposition:                   6128
% 55.25/7.52  sup_immediate_simplified:               170
% 55.25/7.52  sup_given_eliminated:                   0
% 55.25/7.52  comparisons_done:                       0
% 55.25/7.52  comparisons_avoided:                    0
% 55.25/7.52  
% 55.25/7.52  ------ Simplifications
% 55.25/7.52  
% 55.25/7.52  
% 55.25/7.52  sim_fw_subset_subsumed:                 9
% 55.25/7.52  sim_bw_subset_subsumed:                 22
% 55.25/7.52  sim_fw_subsumed:                        104
% 55.25/7.52  sim_bw_subsumed:                        246
% 55.25/7.52  sim_fw_subsumption_res:                 0
% 55.25/7.52  sim_bw_subsumption_res:                 0
% 55.25/7.52  sim_tautology_del:                      364
% 55.25/7.52  sim_eq_tautology_del:                   18
% 55.25/7.52  sim_eq_res_simp:                        6
% 55.25/7.52  sim_fw_demodulated:                     2
% 55.25/7.52  sim_bw_demodulated:                     0
% 55.25/7.52  sim_light_normalised:                   45
% 55.25/7.52  sim_joinable_taut:                      0
% 55.25/7.52  sim_joinable_simp:                      0
% 55.25/7.52  sim_ac_normalised:                      0
% 55.25/7.52  sim_smt_subsumption:                    0
% 55.25/7.52  
%------------------------------------------------------------------------------
