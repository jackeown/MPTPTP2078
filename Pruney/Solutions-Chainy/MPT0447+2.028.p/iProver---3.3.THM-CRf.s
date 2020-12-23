%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:13 EST 2020

% Result     : Theorem 35.42s
% Output     : CNFRefutation 35.42s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 729 expanded)
%              Number of clauses        :  132 ( 207 expanded)
%              Number of leaves         :   33 ( 189 expanded)
%              Depth                    :   18
%              Number of atoms          :  579 (1735 expanded)
%              Number of equality atoms :  260 ( 582 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f42])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f49,f52,f51,f50])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f58,f90])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f74,f75,f75])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f90])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK7))
        & r1_tarski(X0,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(X1))
          & r1_tarski(sK6,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f55,f54])).

fof(f88,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f91])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f69,f77,f91])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f70,f91,f77])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f91])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f72,f91])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | r1_tarski(X0,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f91])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f91])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f91,f91])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1255,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1262,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1245,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1251,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1264,plain,
    ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3568,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1264])).

cnf(c_14447,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1251,c_3568])).

cnf(c_17,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3570,plain,
    ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1264])).

cnf(c_14453,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14447,c_3570])).

cnf(c_14918,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_14453])).

cnf(c_20170,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_14918])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1263,plain,
    ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3563,plain,
    ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X1,X1,X0))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1263])).

cnf(c_4044,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3563,c_1264])).

cnf(c_11593,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_4044])).

cnf(c_20183,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20170,c_11593])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1240,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1259,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2935,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1259])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1253,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4376,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2935,c_1253])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1254,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16570,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4376,c_1254])).

cnf(c_17535,plain,
    ( k6_subset_1(sK6,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1240,c_16570])).

cnf(c_23,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1243,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17909,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_17535,c_1243])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18300,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17909,c_29,c_30])).

cnf(c_20186,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20183,c_18300])).

cnf(c_20373,plain,
    ( k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20186,c_1254])).

cnf(c_1239,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1244,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3412,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1239,c_1244])).

cnf(c_13,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1252,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4244,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
    | r1_tarski(k6_subset_1(X0,k1_relat_1(sK7)),k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_1252])).

cnf(c_20979,plain,
    ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20373,c_4244])).

cnf(c_1238,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3413,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK6),k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1238,c_1244])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1249,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4006,plain,
    ( r1_tarski(k3_relat_1(sK7),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_1249])).

cnf(c_7108,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_4006])).

cnf(c_141533,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X1,X1,X0))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_7108])).

cnf(c_141599,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k1_relat_1(sK6)))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_141533])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1261,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4014,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1261])).

cnf(c_29062,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_4014])).

cnf(c_142410,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK6),k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK7)
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_141599,c_29062])).

cnf(c_142415,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_142410,c_3413])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_641,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1373,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1503,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1317,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK6))
    | ~ r1_tarski(k3_relat_1(sK6),X0)
    | k3_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1387,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(X0,X0,X1)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK6))
    | k3_relat_1(sK6) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_1528,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6))
    | k3_relat_1(sK6) = k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1530,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
    | k3_relat_1(sK6) = k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_642,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1311,plain,
    ( X0 != X1
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1353,plain,
    ( X0 != k3_relat_1(sK7)
    | k3_relat_1(sK7) = X0
    | k3_relat_1(sK7) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_1427,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK7) = k3_tarski(k1_enumset1(X0,X0,X1))
    | k3_tarski(k1_enumset1(X0,X0,X1)) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1770,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK7) = k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_15,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1846,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1848,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_1987,plain,
    ( ~ v1_relat_1(sK7)
    | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2174,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK6))
    | ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6))
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2176,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6))
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
    | ~ r1_tarski(k1_xboole_0,k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_2509,plain,
    ( r1_tarski(k1_xboole_0,k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_647,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1296,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1306,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_3164,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7))
    | k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_3165,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0))
    | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3164])).

cnf(c_3167,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0))
    | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3165])).

cnf(c_1595,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK6))
    | ~ r1_tarski(k3_relat_1(sK6),X0)
    | X0 = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2123,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(X0,X0,X1)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK6))
    | k3_tarski(k1_enumset1(X0,X0,X1)) = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_17062,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_17064,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_17062])).

cnf(c_4378,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_tarski(X3,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X3)),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1253])).

cnf(c_42528,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) != iProver_top
    | r1_tarski(X1,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
    | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_4378])).

cnf(c_42541,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) != iProver_top
    | r1_tarski(X1,k3_relat_1(sK7)) != iProver_top
    | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42528,c_3412])).

cnf(c_44244,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_42541])).

cnf(c_4813,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X2)),k3_relat_1(X3))
    | k3_relat_1(X3) != X1
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_10913,plain,
    ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X1)),k3_relat_1(sK7))
    | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_4813])).

cnf(c_63474,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7))
    | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) != k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10913])).

cnf(c_63475,plain,
    ( k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) != k3_relat_1(sK6)
    | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63474])).

cnf(c_63477,plain,
    ( k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) != k3_relat_1(sK6)
    | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_63475])).

cnf(c_25810,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ r1_tarski(k6_subset_1(X0,k1_relat_1(sK7)),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_86638,plain,
    ( ~ r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7))
    | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) ),
    inference(instantiation,[status(thm)],[c_25810])).

cnf(c_86642,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7)) != iProver_top
    | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86638])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,sK2(X0,X1,X2))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1256,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK2(X0,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,sK2(X0,X1,X2))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1258,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,sK2(X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6145,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1258])).

cnf(c_82,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_116198,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6145,c_82])).

cnf(c_116212,plain,
    ( k3_tarski(k1_enumset1(sK7,sK7,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_1240,c_116198])).

cnf(c_117780,plain,
    ( k3_tarski(k1_enumset1(sK6,sK6,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_17,c_116212])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1242,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1779,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k2_relat_1(X0))) = k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1242])).

cnf(c_2196,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k2_relat_1(sK7))) = k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,sK7))) ),
    inference(superposition,[status(thm)],[c_1239,c_1779])).

cnf(c_1250,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2198,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_1250])).

cnf(c_117963,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_117780,c_2198])).

cnf(c_3661,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_1259])).

cnf(c_119916,plain,
    ( r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_117963,c_3661])).

cnf(c_142964,plain,
    ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_142415,c_27,c_32,c_1373,c_1503,c_1530,c_1770,c_1848,c_1987,c_2176,c_2509,c_3167,c_17064,c_44244,c_63477,c_86642,c_119916])).

cnf(c_142968,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20979,c_142964])).

cnf(c_146008,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1255,c_142968])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 35.42/5.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.42/5.02  
% 35.42/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.42/5.02  
% 35.42/5.02  ------  iProver source info
% 35.42/5.02  
% 35.42/5.02  git: date: 2020-06-30 10:37:57 +0100
% 35.42/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.42/5.02  git: non_committed_changes: false
% 35.42/5.02  git: last_make_outside_of_git: false
% 35.42/5.02  
% 35.42/5.02  ------ 
% 35.42/5.02  
% 35.42/5.02  ------ Input Options
% 35.42/5.02  
% 35.42/5.02  --out_options                           all
% 35.42/5.02  --tptp_safe_out                         true
% 35.42/5.02  --problem_path                          ""
% 35.42/5.02  --include_path                          ""
% 35.42/5.02  --clausifier                            res/vclausify_rel
% 35.42/5.02  --clausifier_options                    ""
% 35.42/5.02  --stdin                                 false
% 35.42/5.02  --stats_out                             all
% 35.42/5.02  
% 35.42/5.02  ------ General Options
% 35.42/5.02  
% 35.42/5.02  --fof                                   false
% 35.42/5.02  --time_out_real                         305.
% 35.42/5.02  --time_out_virtual                      -1.
% 35.42/5.02  --symbol_type_check                     false
% 35.42/5.02  --clausify_out                          false
% 35.42/5.02  --sig_cnt_out                           false
% 35.42/5.02  --trig_cnt_out                          false
% 35.42/5.02  --trig_cnt_out_tolerance                1.
% 35.42/5.02  --trig_cnt_out_sk_spl                   false
% 35.42/5.02  --abstr_cl_out                          false
% 35.42/5.02  
% 35.42/5.02  ------ Global Options
% 35.42/5.02  
% 35.42/5.02  --schedule                              default
% 35.42/5.02  --add_important_lit                     false
% 35.42/5.02  --prop_solver_per_cl                    1000
% 35.42/5.02  --min_unsat_core                        false
% 35.42/5.02  --soft_assumptions                      false
% 35.42/5.02  --soft_lemma_size                       3
% 35.42/5.02  --prop_impl_unit_size                   0
% 35.42/5.02  --prop_impl_unit                        []
% 35.42/5.02  --share_sel_clauses                     true
% 35.42/5.02  --reset_solvers                         false
% 35.42/5.02  --bc_imp_inh                            [conj_cone]
% 35.42/5.02  --conj_cone_tolerance                   3.
% 35.42/5.02  --extra_neg_conj                        none
% 35.42/5.02  --large_theory_mode                     true
% 35.42/5.02  --prolific_symb_bound                   200
% 35.42/5.02  --lt_threshold                          2000
% 35.42/5.02  --clause_weak_htbl                      true
% 35.42/5.02  --gc_record_bc_elim                     false
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing Options
% 35.42/5.02  
% 35.42/5.02  --preprocessing_flag                    true
% 35.42/5.02  --time_out_prep_mult                    0.1
% 35.42/5.02  --splitting_mode                        input
% 35.42/5.02  --splitting_grd                         true
% 35.42/5.02  --splitting_cvd                         false
% 35.42/5.02  --splitting_cvd_svl                     false
% 35.42/5.02  --splitting_nvd                         32
% 35.42/5.02  --sub_typing                            true
% 35.42/5.02  --prep_gs_sim                           true
% 35.42/5.02  --prep_unflatten                        true
% 35.42/5.02  --prep_res_sim                          true
% 35.42/5.02  --prep_upred                            true
% 35.42/5.02  --prep_sem_filter                       exhaustive
% 35.42/5.02  --prep_sem_filter_out                   false
% 35.42/5.02  --pred_elim                             true
% 35.42/5.02  --res_sim_input                         true
% 35.42/5.02  --eq_ax_congr_red                       true
% 35.42/5.02  --pure_diseq_elim                       true
% 35.42/5.02  --brand_transform                       false
% 35.42/5.02  --non_eq_to_eq                          false
% 35.42/5.02  --prep_def_merge                        true
% 35.42/5.02  --prep_def_merge_prop_impl              false
% 35.42/5.02  --prep_def_merge_mbd                    true
% 35.42/5.02  --prep_def_merge_tr_red                 false
% 35.42/5.02  --prep_def_merge_tr_cl                  false
% 35.42/5.02  --smt_preprocessing                     true
% 35.42/5.02  --smt_ac_axioms                         fast
% 35.42/5.02  --preprocessed_out                      false
% 35.42/5.02  --preprocessed_stats                    false
% 35.42/5.02  
% 35.42/5.02  ------ Abstraction refinement Options
% 35.42/5.02  
% 35.42/5.02  --abstr_ref                             []
% 35.42/5.02  --abstr_ref_prep                        false
% 35.42/5.02  --abstr_ref_until_sat                   false
% 35.42/5.02  --abstr_ref_sig_restrict                funpre
% 35.42/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 35.42/5.02  --abstr_ref_under                       []
% 35.42/5.02  
% 35.42/5.02  ------ SAT Options
% 35.42/5.02  
% 35.42/5.02  --sat_mode                              false
% 35.42/5.02  --sat_fm_restart_options                ""
% 35.42/5.02  --sat_gr_def                            false
% 35.42/5.02  --sat_epr_types                         true
% 35.42/5.02  --sat_non_cyclic_types                  false
% 35.42/5.02  --sat_finite_models                     false
% 35.42/5.02  --sat_fm_lemmas                         false
% 35.42/5.02  --sat_fm_prep                           false
% 35.42/5.02  --sat_fm_uc_incr                        true
% 35.42/5.02  --sat_out_model                         small
% 35.42/5.02  --sat_out_clauses                       false
% 35.42/5.02  
% 35.42/5.02  ------ QBF Options
% 35.42/5.02  
% 35.42/5.02  --qbf_mode                              false
% 35.42/5.02  --qbf_elim_univ                         false
% 35.42/5.02  --qbf_dom_inst                          none
% 35.42/5.02  --qbf_dom_pre_inst                      false
% 35.42/5.02  --qbf_sk_in                             false
% 35.42/5.02  --qbf_pred_elim                         true
% 35.42/5.02  --qbf_split                             512
% 35.42/5.02  
% 35.42/5.02  ------ BMC1 Options
% 35.42/5.02  
% 35.42/5.02  --bmc1_incremental                      false
% 35.42/5.02  --bmc1_axioms                           reachable_all
% 35.42/5.02  --bmc1_min_bound                        0
% 35.42/5.02  --bmc1_max_bound                        -1
% 35.42/5.02  --bmc1_max_bound_default                -1
% 35.42/5.02  --bmc1_symbol_reachability              true
% 35.42/5.02  --bmc1_property_lemmas                  false
% 35.42/5.02  --bmc1_k_induction                      false
% 35.42/5.02  --bmc1_non_equiv_states                 false
% 35.42/5.02  --bmc1_deadlock                         false
% 35.42/5.02  --bmc1_ucm                              false
% 35.42/5.02  --bmc1_add_unsat_core                   none
% 35.42/5.02  --bmc1_unsat_core_children              false
% 35.42/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 35.42/5.02  --bmc1_out_stat                         full
% 35.42/5.02  --bmc1_ground_init                      false
% 35.42/5.02  --bmc1_pre_inst_next_state              false
% 35.42/5.02  --bmc1_pre_inst_state                   false
% 35.42/5.02  --bmc1_pre_inst_reach_state             false
% 35.42/5.02  --bmc1_out_unsat_core                   false
% 35.42/5.02  --bmc1_aig_witness_out                  false
% 35.42/5.02  --bmc1_verbose                          false
% 35.42/5.02  --bmc1_dump_clauses_tptp                false
% 35.42/5.02  --bmc1_dump_unsat_core_tptp             false
% 35.42/5.02  --bmc1_dump_file                        -
% 35.42/5.02  --bmc1_ucm_expand_uc_limit              128
% 35.42/5.02  --bmc1_ucm_n_expand_iterations          6
% 35.42/5.02  --bmc1_ucm_extend_mode                  1
% 35.42/5.02  --bmc1_ucm_init_mode                    2
% 35.42/5.02  --bmc1_ucm_cone_mode                    none
% 35.42/5.02  --bmc1_ucm_reduced_relation_type        0
% 35.42/5.02  --bmc1_ucm_relax_model                  4
% 35.42/5.02  --bmc1_ucm_full_tr_after_sat            true
% 35.42/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 35.42/5.02  --bmc1_ucm_layered_model                none
% 35.42/5.02  --bmc1_ucm_max_lemma_size               10
% 35.42/5.02  
% 35.42/5.02  ------ AIG Options
% 35.42/5.02  
% 35.42/5.02  --aig_mode                              false
% 35.42/5.02  
% 35.42/5.02  ------ Instantiation Options
% 35.42/5.02  
% 35.42/5.02  --instantiation_flag                    true
% 35.42/5.02  --inst_sos_flag                         true
% 35.42/5.02  --inst_sos_phase                        true
% 35.42/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.42/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.42/5.02  --inst_lit_sel_side                     num_symb
% 35.42/5.02  --inst_solver_per_active                1400
% 35.42/5.02  --inst_solver_calls_frac                1.
% 35.42/5.02  --inst_passive_queue_type               priority_queues
% 35.42/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.42/5.02  --inst_passive_queues_freq              [25;2]
% 35.42/5.02  --inst_dismatching                      true
% 35.42/5.02  --inst_eager_unprocessed_to_passive     true
% 35.42/5.02  --inst_prop_sim_given                   true
% 35.42/5.02  --inst_prop_sim_new                     false
% 35.42/5.02  --inst_subs_new                         false
% 35.42/5.02  --inst_eq_res_simp                      false
% 35.42/5.02  --inst_subs_given                       false
% 35.42/5.02  --inst_orphan_elimination               true
% 35.42/5.02  --inst_learning_loop_flag               true
% 35.42/5.02  --inst_learning_start                   3000
% 35.42/5.02  --inst_learning_factor                  2
% 35.42/5.02  --inst_start_prop_sim_after_learn       3
% 35.42/5.02  --inst_sel_renew                        solver
% 35.42/5.02  --inst_lit_activity_flag                true
% 35.42/5.02  --inst_restr_to_given                   false
% 35.42/5.02  --inst_activity_threshold               500
% 35.42/5.02  --inst_out_proof                        true
% 35.42/5.02  
% 35.42/5.02  ------ Resolution Options
% 35.42/5.02  
% 35.42/5.02  --resolution_flag                       true
% 35.42/5.02  --res_lit_sel                           adaptive
% 35.42/5.02  --res_lit_sel_side                      none
% 35.42/5.02  --res_ordering                          kbo
% 35.42/5.02  --res_to_prop_solver                    active
% 35.42/5.02  --res_prop_simpl_new                    false
% 35.42/5.02  --res_prop_simpl_given                  true
% 35.42/5.02  --res_passive_queue_type                priority_queues
% 35.42/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.42/5.02  --res_passive_queues_freq               [15;5]
% 35.42/5.02  --res_forward_subs                      full
% 35.42/5.02  --res_backward_subs                     full
% 35.42/5.02  --res_forward_subs_resolution           true
% 35.42/5.02  --res_backward_subs_resolution          true
% 35.42/5.02  --res_orphan_elimination                true
% 35.42/5.02  --res_time_limit                        2.
% 35.42/5.02  --res_out_proof                         true
% 35.42/5.02  
% 35.42/5.02  ------ Superposition Options
% 35.42/5.02  
% 35.42/5.02  --superposition_flag                    true
% 35.42/5.02  --sup_passive_queue_type                priority_queues
% 35.42/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.42/5.02  --sup_passive_queues_freq               [8;1;4]
% 35.42/5.02  --demod_completeness_check              fast
% 35.42/5.02  --demod_use_ground                      true
% 35.42/5.02  --sup_to_prop_solver                    passive
% 35.42/5.02  --sup_prop_simpl_new                    true
% 35.42/5.02  --sup_prop_simpl_given                  true
% 35.42/5.02  --sup_fun_splitting                     true
% 35.42/5.02  --sup_smt_interval                      50000
% 35.42/5.02  
% 35.42/5.02  ------ Superposition Simplification Setup
% 35.42/5.02  
% 35.42/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.42/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.42/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.42/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.42/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 35.42/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.42/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.42/5.02  --sup_immed_triv                        [TrivRules]
% 35.42/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_immed_bw_main                     []
% 35.42/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.42/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 35.42/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_input_bw                          []
% 35.42/5.02  
% 35.42/5.02  ------ Combination Options
% 35.42/5.02  
% 35.42/5.02  --comb_res_mult                         3
% 35.42/5.02  --comb_sup_mult                         2
% 35.42/5.02  --comb_inst_mult                        10
% 35.42/5.02  
% 35.42/5.02  ------ Debug Options
% 35.42/5.02  
% 35.42/5.02  --dbg_backtrace                         false
% 35.42/5.02  --dbg_dump_prop_clauses                 false
% 35.42/5.02  --dbg_dump_prop_clauses_file            -
% 35.42/5.02  --dbg_out_stat                          false
% 35.42/5.02  ------ Parsing...
% 35.42/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.42/5.02  ------ Proving...
% 35.42/5.02  ------ Problem Properties 
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  clauses                                 28
% 35.42/5.02  conjectures                             4
% 35.42/5.02  EPR                                     8
% 35.42/5.02  Horn                                    23
% 35.42/5.02  unary                                   9
% 35.42/5.02  binary                                  10
% 35.42/5.02  lits                                    59
% 35.42/5.02  lits eq                                 11
% 35.42/5.02  fd_pure                                 0
% 35.42/5.02  fd_pseudo                               0
% 35.42/5.02  fd_cond                                 2
% 35.42/5.02  fd_pseudo_cond                          6
% 35.42/5.02  AC symbols                              0
% 35.42/5.02  
% 35.42/5.02  ------ Schedule dynamic 5 is on 
% 35.42/5.02  
% 35.42/5.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  ------ 
% 35.42/5.02  Current options:
% 35.42/5.02  ------ 
% 35.42/5.02  
% 35.42/5.02  ------ Input Options
% 35.42/5.02  
% 35.42/5.02  --out_options                           all
% 35.42/5.02  --tptp_safe_out                         true
% 35.42/5.02  --problem_path                          ""
% 35.42/5.02  --include_path                          ""
% 35.42/5.02  --clausifier                            res/vclausify_rel
% 35.42/5.02  --clausifier_options                    ""
% 35.42/5.02  --stdin                                 false
% 35.42/5.02  --stats_out                             all
% 35.42/5.02  
% 35.42/5.02  ------ General Options
% 35.42/5.02  
% 35.42/5.02  --fof                                   false
% 35.42/5.02  --time_out_real                         305.
% 35.42/5.02  --time_out_virtual                      -1.
% 35.42/5.02  --symbol_type_check                     false
% 35.42/5.02  --clausify_out                          false
% 35.42/5.02  --sig_cnt_out                           false
% 35.42/5.02  --trig_cnt_out                          false
% 35.42/5.02  --trig_cnt_out_tolerance                1.
% 35.42/5.02  --trig_cnt_out_sk_spl                   false
% 35.42/5.02  --abstr_cl_out                          false
% 35.42/5.02  
% 35.42/5.02  ------ Global Options
% 35.42/5.02  
% 35.42/5.02  --schedule                              default
% 35.42/5.02  --add_important_lit                     false
% 35.42/5.02  --prop_solver_per_cl                    1000
% 35.42/5.02  --min_unsat_core                        false
% 35.42/5.02  --soft_assumptions                      false
% 35.42/5.02  --soft_lemma_size                       3
% 35.42/5.02  --prop_impl_unit_size                   0
% 35.42/5.02  --prop_impl_unit                        []
% 35.42/5.02  --share_sel_clauses                     true
% 35.42/5.02  --reset_solvers                         false
% 35.42/5.02  --bc_imp_inh                            [conj_cone]
% 35.42/5.02  --conj_cone_tolerance                   3.
% 35.42/5.02  --extra_neg_conj                        none
% 35.42/5.02  --large_theory_mode                     true
% 35.42/5.02  --prolific_symb_bound                   200
% 35.42/5.02  --lt_threshold                          2000
% 35.42/5.02  --clause_weak_htbl                      true
% 35.42/5.02  --gc_record_bc_elim                     false
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing Options
% 35.42/5.02  
% 35.42/5.02  --preprocessing_flag                    true
% 35.42/5.02  --time_out_prep_mult                    0.1
% 35.42/5.02  --splitting_mode                        input
% 35.42/5.02  --splitting_grd                         true
% 35.42/5.02  --splitting_cvd                         false
% 35.42/5.02  --splitting_cvd_svl                     false
% 35.42/5.02  --splitting_nvd                         32
% 35.42/5.02  --sub_typing                            true
% 35.42/5.02  --prep_gs_sim                           true
% 35.42/5.02  --prep_unflatten                        true
% 35.42/5.02  --prep_res_sim                          true
% 35.42/5.02  --prep_upred                            true
% 35.42/5.02  --prep_sem_filter                       exhaustive
% 35.42/5.02  --prep_sem_filter_out                   false
% 35.42/5.02  --pred_elim                             true
% 35.42/5.02  --res_sim_input                         true
% 35.42/5.02  --eq_ax_congr_red                       true
% 35.42/5.02  --pure_diseq_elim                       true
% 35.42/5.02  --brand_transform                       false
% 35.42/5.02  --non_eq_to_eq                          false
% 35.42/5.02  --prep_def_merge                        true
% 35.42/5.02  --prep_def_merge_prop_impl              false
% 35.42/5.02  --prep_def_merge_mbd                    true
% 35.42/5.02  --prep_def_merge_tr_red                 false
% 35.42/5.02  --prep_def_merge_tr_cl                  false
% 35.42/5.02  --smt_preprocessing                     true
% 35.42/5.02  --smt_ac_axioms                         fast
% 35.42/5.02  --preprocessed_out                      false
% 35.42/5.02  --preprocessed_stats                    false
% 35.42/5.02  
% 35.42/5.02  ------ Abstraction refinement Options
% 35.42/5.02  
% 35.42/5.02  --abstr_ref                             []
% 35.42/5.02  --abstr_ref_prep                        false
% 35.42/5.02  --abstr_ref_until_sat                   false
% 35.42/5.02  --abstr_ref_sig_restrict                funpre
% 35.42/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 35.42/5.02  --abstr_ref_under                       []
% 35.42/5.02  
% 35.42/5.02  ------ SAT Options
% 35.42/5.02  
% 35.42/5.02  --sat_mode                              false
% 35.42/5.02  --sat_fm_restart_options                ""
% 35.42/5.02  --sat_gr_def                            false
% 35.42/5.02  --sat_epr_types                         true
% 35.42/5.02  --sat_non_cyclic_types                  false
% 35.42/5.02  --sat_finite_models                     false
% 35.42/5.02  --sat_fm_lemmas                         false
% 35.42/5.02  --sat_fm_prep                           false
% 35.42/5.02  --sat_fm_uc_incr                        true
% 35.42/5.02  --sat_out_model                         small
% 35.42/5.02  --sat_out_clauses                       false
% 35.42/5.02  
% 35.42/5.02  ------ QBF Options
% 35.42/5.02  
% 35.42/5.02  --qbf_mode                              false
% 35.42/5.02  --qbf_elim_univ                         false
% 35.42/5.02  --qbf_dom_inst                          none
% 35.42/5.02  --qbf_dom_pre_inst                      false
% 35.42/5.02  --qbf_sk_in                             false
% 35.42/5.02  --qbf_pred_elim                         true
% 35.42/5.02  --qbf_split                             512
% 35.42/5.02  
% 35.42/5.02  ------ BMC1 Options
% 35.42/5.02  
% 35.42/5.02  --bmc1_incremental                      false
% 35.42/5.02  --bmc1_axioms                           reachable_all
% 35.42/5.02  --bmc1_min_bound                        0
% 35.42/5.02  --bmc1_max_bound                        -1
% 35.42/5.02  --bmc1_max_bound_default                -1
% 35.42/5.02  --bmc1_symbol_reachability              true
% 35.42/5.02  --bmc1_property_lemmas                  false
% 35.42/5.02  --bmc1_k_induction                      false
% 35.42/5.02  --bmc1_non_equiv_states                 false
% 35.42/5.02  --bmc1_deadlock                         false
% 35.42/5.02  --bmc1_ucm                              false
% 35.42/5.02  --bmc1_add_unsat_core                   none
% 35.42/5.02  --bmc1_unsat_core_children              false
% 35.42/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 35.42/5.02  --bmc1_out_stat                         full
% 35.42/5.02  --bmc1_ground_init                      false
% 35.42/5.02  --bmc1_pre_inst_next_state              false
% 35.42/5.02  --bmc1_pre_inst_state                   false
% 35.42/5.02  --bmc1_pre_inst_reach_state             false
% 35.42/5.02  --bmc1_out_unsat_core                   false
% 35.42/5.02  --bmc1_aig_witness_out                  false
% 35.42/5.02  --bmc1_verbose                          false
% 35.42/5.02  --bmc1_dump_clauses_tptp                false
% 35.42/5.02  --bmc1_dump_unsat_core_tptp             false
% 35.42/5.02  --bmc1_dump_file                        -
% 35.42/5.02  --bmc1_ucm_expand_uc_limit              128
% 35.42/5.02  --bmc1_ucm_n_expand_iterations          6
% 35.42/5.02  --bmc1_ucm_extend_mode                  1
% 35.42/5.02  --bmc1_ucm_init_mode                    2
% 35.42/5.02  --bmc1_ucm_cone_mode                    none
% 35.42/5.02  --bmc1_ucm_reduced_relation_type        0
% 35.42/5.02  --bmc1_ucm_relax_model                  4
% 35.42/5.02  --bmc1_ucm_full_tr_after_sat            true
% 35.42/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 35.42/5.02  --bmc1_ucm_layered_model                none
% 35.42/5.02  --bmc1_ucm_max_lemma_size               10
% 35.42/5.02  
% 35.42/5.02  ------ AIG Options
% 35.42/5.02  
% 35.42/5.02  --aig_mode                              false
% 35.42/5.02  
% 35.42/5.02  ------ Instantiation Options
% 35.42/5.02  
% 35.42/5.02  --instantiation_flag                    true
% 35.42/5.02  --inst_sos_flag                         true
% 35.42/5.02  --inst_sos_phase                        true
% 35.42/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.42/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.42/5.02  --inst_lit_sel_side                     none
% 35.42/5.02  --inst_solver_per_active                1400
% 35.42/5.02  --inst_solver_calls_frac                1.
% 35.42/5.02  --inst_passive_queue_type               priority_queues
% 35.42/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.42/5.02  --inst_passive_queues_freq              [25;2]
% 35.42/5.02  --inst_dismatching                      true
% 35.42/5.02  --inst_eager_unprocessed_to_passive     true
% 35.42/5.02  --inst_prop_sim_given                   true
% 35.42/5.02  --inst_prop_sim_new                     false
% 35.42/5.02  --inst_subs_new                         false
% 35.42/5.02  --inst_eq_res_simp                      false
% 35.42/5.02  --inst_subs_given                       false
% 35.42/5.02  --inst_orphan_elimination               true
% 35.42/5.02  --inst_learning_loop_flag               true
% 35.42/5.02  --inst_learning_start                   3000
% 35.42/5.02  --inst_learning_factor                  2
% 35.42/5.02  --inst_start_prop_sim_after_learn       3
% 35.42/5.02  --inst_sel_renew                        solver
% 35.42/5.02  --inst_lit_activity_flag                true
% 35.42/5.02  --inst_restr_to_given                   false
% 35.42/5.02  --inst_activity_threshold               500
% 35.42/5.02  --inst_out_proof                        true
% 35.42/5.02  
% 35.42/5.02  ------ Resolution Options
% 35.42/5.02  
% 35.42/5.02  --resolution_flag                       false
% 35.42/5.02  --res_lit_sel                           adaptive
% 35.42/5.02  --res_lit_sel_side                      none
% 35.42/5.02  --res_ordering                          kbo
% 35.42/5.02  --res_to_prop_solver                    active
% 35.42/5.02  --res_prop_simpl_new                    false
% 35.42/5.02  --res_prop_simpl_given                  true
% 35.42/5.02  --res_passive_queue_type                priority_queues
% 35.42/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.42/5.02  --res_passive_queues_freq               [15;5]
% 35.42/5.02  --res_forward_subs                      full
% 35.42/5.02  --res_backward_subs                     full
% 35.42/5.02  --res_forward_subs_resolution           true
% 35.42/5.02  --res_backward_subs_resolution          true
% 35.42/5.02  --res_orphan_elimination                true
% 35.42/5.02  --res_time_limit                        2.
% 35.42/5.02  --res_out_proof                         true
% 35.42/5.02  
% 35.42/5.02  ------ Superposition Options
% 35.42/5.02  
% 35.42/5.02  --superposition_flag                    true
% 35.42/5.02  --sup_passive_queue_type                priority_queues
% 35.42/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.42/5.02  --sup_passive_queues_freq               [8;1;4]
% 35.42/5.02  --demod_completeness_check              fast
% 35.42/5.02  --demod_use_ground                      true
% 35.42/5.02  --sup_to_prop_solver                    passive
% 35.42/5.02  --sup_prop_simpl_new                    true
% 35.42/5.02  --sup_prop_simpl_given                  true
% 35.42/5.02  --sup_fun_splitting                     true
% 35.42/5.02  --sup_smt_interval                      50000
% 35.42/5.02  
% 35.42/5.02  ------ Superposition Simplification Setup
% 35.42/5.02  
% 35.42/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.42/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.42/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.42/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.42/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 35.42/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.42/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.42/5.02  --sup_immed_triv                        [TrivRules]
% 35.42/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_immed_bw_main                     []
% 35.42/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.42/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 35.42/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.42/5.02  --sup_input_bw                          []
% 35.42/5.02  
% 35.42/5.02  ------ Combination Options
% 35.42/5.02  
% 35.42/5.02  --comb_res_mult                         3
% 35.42/5.02  --comb_sup_mult                         2
% 35.42/5.02  --comb_inst_mult                        10
% 35.42/5.02  
% 35.42/5.02  ------ Debug Options
% 35.42/5.02  
% 35.42/5.02  --dbg_backtrace                         false
% 35.42/5.02  --dbg_dump_prop_clauses                 false
% 35.42/5.02  --dbg_dump_prop_clauses_file            -
% 35.42/5.02  --dbg_out_stat                          false
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  ------ Proving...
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  % SZS status Theorem for theBenchmark.p
% 35.42/5.02  
% 35.42/5.02   Resolution empty clause
% 35.42/5.02  
% 35.42/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 35.42/5.02  
% 35.42/5.02  fof(f6,axiom,(
% 35.42/5.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f67,plain,(
% 35.42/5.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f6])).
% 35.42/5.02  
% 35.42/5.02  fof(f2,axiom,(
% 35.42/5.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f26,plain,(
% 35.42/5.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 35.42/5.02    inference(ennf_transformation,[],[f2])).
% 35.42/5.02  
% 35.42/5.02  fof(f42,plain,(
% 35.42/5.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f43,plain,(
% 35.42/5.02    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 35.42/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f42])).
% 35.42/5.02  
% 35.42/5.02  fof(f59,plain,(
% 35.42/5.02    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 35.42/5.02    inference(cnf_transformation,[],[f43])).
% 35.42/5.02  
% 35.42/5.02  fof(f18,axiom,(
% 35.42/5.02    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f48,plain,(
% 35.42/5.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 35.42/5.02    inference(nnf_transformation,[],[f18])).
% 35.42/5.02  
% 35.42/5.02  fof(f49,plain,(
% 35.42/5.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 35.42/5.02    inference(rectify,[],[f48])).
% 35.42/5.02  
% 35.42/5.02  fof(f52,plain,(
% 35.42/5.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f51,plain,(
% 35.42/5.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f50,plain,(
% 35.42/5.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f53,plain,(
% 35.42/5.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 35.42/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f49,f52,f51,f50])).
% 35.42/5.02  
% 35.42/5.02  fof(f79,plain,(
% 35.42/5.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 35.42/5.02    inference(cnf_transformation,[],[f53])).
% 35.42/5.02  
% 35.42/5.02  fof(f108,plain,(
% 35.42/5.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 35.42/5.02    inference(equality_resolution,[],[f79])).
% 35.42/5.02  
% 35.42/5.02  fof(f10,axiom,(
% 35.42/5.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f71,plain,(
% 35.42/5.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f10])).
% 35.42/5.02  
% 35.42/5.02  fof(f1,axiom,(
% 35.42/5.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f24,plain,(
% 35.42/5.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.42/5.02    inference(rectify,[],[f1])).
% 35.42/5.02  
% 35.42/5.02  fof(f25,plain,(
% 35.42/5.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.42/5.02    inference(ennf_transformation,[],[f24])).
% 35.42/5.02  
% 35.42/5.02  fof(f40,plain,(
% 35.42/5.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f41,plain,(
% 35.42/5.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.42/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f40])).
% 35.42/5.02  
% 35.42/5.02  fof(f58,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.42/5.02    inference(cnf_transformation,[],[f41])).
% 35.42/5.02  
% 35.42/5.02  fof(f17,axiom,(
% 35.42/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f78,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.42/5.02    inference(cnf_transformation,[],[f17])).
% 35.42/5.02  
% 35.42/5.02  fof(f14,axiom,(
% 35.42/5.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f75,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f14])).
% 35.42/5.02  
% 35.42/5.02  fof(f90,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 35.42/5.02    inference(definition_unfolding,[],[f78,f75])).
% 35.42/5.02  
% 35.42/5.02  fof(f92,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 35.42/5.02    inference(definition_unfolding,[],[f58,f90])).
% 35.42/5.02  
% 35.42/5.02  fof(f13,axiom,(
% 35.42/5.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f74,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f13])).
% 35.42/5.02  
% 35.42/5.02  fof(f102,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f74,f75,f75])).
% 35.42/5.02  
% 35.42/5.02  fof(f57,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f41])).
% 35.42/5.02  
% 35.42/5.02  fof(f93,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f57,f90])).
% 35.42/5.02  
% 35.42/5.02  fof(f22,conjecture,(
% 35.42/5.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f23,negated_conjecture,(
% 35.42/5.02    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.42/5.02    inference(negated_conjecture,[],[f22])).
% 35.42/5.02  
% 35.42/5.02  fof(f38,plain,(
% 35.42/5.02    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.42/5.02    inference(ennf_transformation,[],[f23])).
% 35.42/5.02  
% 35.42/5.02  fof(f39,plain,(
% 35.42/5.02    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.42/5.02    inference(flattening,[],[f38])).
% 35.42/5.02  
% 35.42/5.02  fof(f55,plain,(
% 35.42/5.02    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK7)) & r1_tarski(X0,sK7) & v1_relat_1(sK7))) )),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f54,plain,(
% 35.42/5.02    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK6),k3_relat_1(X1)) & r1_tarski(sK6,X1) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f56,plain,(
% 35.42/5.02    (~r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 35.42/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f55,f54])).
% 35.42/5.02  
% 35.42/5.02  fof(f88,plain,(
% 35.42/5.02    r1_tarski(sK6,sK7)),
% 35.42/5.02    inference(cnf_transformation,[],[f56])).
% 35.42/5.02  
% 35.42/5.02  fof(f4,axiom,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f27,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.42/5.02    inference(ennf_transformation,[],[f4])).
% 35.42/5.02  
% 35.42/5.02  fof(f63,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f27])).
% 35.42/5.02  
% 35.42/5.02  fof(f15,axiom,(
% 35.42/5.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f76,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.42/5.02    inference(cnf_transformation,[],[f15])).
% 35.42/5.02  
% 35.42/5.02  fof(f91,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 35.42/5.02    inference(definition_unfolding,[],[f76,f75])).
% 35.42/5.02  
% 35.42/5.02  fof(f94,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f63,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f8,axiom,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f31,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.42/5.02    inference(ennf_transformation,[],[f8])).
% 35.42/5.02  
% 35.42/5.02  fof(f69,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.42/5.02    inference(cnf_transformation,[],[f31])).
% 35.42/5.02  
% 35.42/5.02  fof(f16,axiom,(
% 35.42/5.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f77,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f16])).
% 35.42/5.02  
% 35.42/5.02  fof(f98,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 35.42/5.02    inference(definition_unfolding,[],[f69,f77,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f7,axiom,(
% 35.42/5.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f30,plain,(
% 35.42/5.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 35.42/5.02    inference(ennf_transformation,[],[f7])).
% 35.42/5.02  
% 35.42/5.02  fof(f68,plain,(
% 35.42/5.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f30])).
% 35.42/5.02  
% 35.42/5.02  fof(f20,axiom,(
% 35.42/5.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f36,plain,(
% 35.42/5.02    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.42/5.02    inference(ennf_transformation,[],[f20])).
% 35.42/5.02  
% 35.42/5.02  fof(f84,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f36])).
% 35.42/5.02  
% 35.42/5.02  fof(f86,plain,(
% 35.42/5.02    v1_relat_1(sK6)),
% 35.42/5.02    inference(cnf_transformation,[],[f56])).
% 35.42/5.02  
% 35.42/5.02  fof(f87,plain,(
% 35.42/5.02    v1_relat_1(sK7)),
% 35.42/5.02    inference(cnf_transformation,[],[f56])).
% 35.42/5.02  
% 35.42/5.02  fof(f19,axiom,(
% 35.42/5.02    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f35,plain,(
% 35.42/5.02    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 35.42/5.02    inference(ennf_transformation,[],[f19])).
% 35.42/5.02  
% 35.42/5.02  fof(f83,plain,(
% 35.42/5.02    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f35])).
% 35.42/5.02  
% 35.42/5.02  fof(f103,plain,(
% 35.42/5.02    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f83,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f9,axiom,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f32,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.42/5.02    inference(ennf_transformation,[],[f9])).
% 35.42/5.02  
% 35.42/5.02  fof(f70,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f32])).
% 35.42/5.02  
% 35.42/5.02  fof(f99,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f70,f91,f77])).
% 35.42/5.02  
% 35.42/5.02  fof(f12,axiom,(
% 35.42/5.02    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f33,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.42/5.02    inference(ennf_transformation,[],[f12])).
% 35.42/5.02  
% 35.42/5.02  fof(f34,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.42/5.02    inference(flattening,[],[f33])).
% 35.42/5.02  
% 35.42/5.02  fof(f73,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f34])).
% 35.42/5.02  
% 35.42/5.02  fof(f101,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f73,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f3,axiom,(
% 35.42/5.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f44,plain,(
% 35.42/5.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.42/5.02    inference(nnf_transformation,[],[f3])).
% 35.42/5.02  
% 35.42/5.02  fof(f45,plain,(
% 35.42/5.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.42/5.02    inference(flattening,[],[f44])).
% 35.42/5.02  
% 35.42/5.02  fof(f62,plain,(
% 35.42/5.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f45])).
% 35.42/5.02  
% 35.42/5.02  fof(f89,plain,(
% 35.42/5.02    ~r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))),
% 35.42/5.02    inference(cnf_transformation,[],[f56])).
% 35.42/5.02  
% 35.42/5.02  fof(f60,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.42/5.02    inference(cnf_transformation,[],[f45])).
% 35.42/5.02  
% 35.42/5.02  fof(f106,plain,(
% 35.42/5.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.42/5.02    inference(equality_resolution,[],[f60])).
% 35.42/5.02  
% 35.42/5.02  fof(f11,axiom,(
% 35.42/5.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f72,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.42/5.02    inference(cnf_transformation,[],[f11])).
% 35.42/5.02  
% 35.42/5.02  fof(f100,plain,(
% 35.42/5.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 35.42/5.02    inference(definition_unfolding,[],[f72,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f5,axiom,(
% 35.42/5.02    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f28,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.42/5.02    inference(ennf_transformation,[],[f5])).
% 35.42/5.02  
% 35.42/5.02  fof(f29,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.42/5.02    inference(flattening,[],[f28])).
% 35.42/5.02  
% 35.42/5.02  fof(f46,plain,(
% 35.42/5.02    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))))),
% 35.42/5.02    introduced(choice_axiom,[])).
% 35.42/5.02  
% 35.42/5.02  fof(f47,plain,(
% 35.42/5.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.42/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f46])).
% 35.42/5.02  
% 35.42/5.02  fof(f64,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f47])).
% 35.42/5.02  
% 35.42/5.02  fof(f97,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | r1_tarski(X0,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f64,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f66,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f47])).
% 35.42/5.02  
% 35.42/5.02  fof(f95,plain,(
% 35.42/5.02    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X1,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f66,f91])).
% 35.42/5.02  
% 35.42/5.02  fof(f21,axiom,(
% 35.42/5.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 35.42/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.42/5.02  
% 35.42/5.02  fof(f37,plain,(
% 35.42/5.02    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.42/5.02    inference(ennf_transformation,[],[f21])).
% 35.42/5.02  
% 35.42/5.02  fof(f85,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.42/5.02    inference(cnf_transformation,[],[f37])).
% 35.42/5.02  
% 35.42/5.02  fof(f104,plain,(
% 35.42/5.02    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.42/5.02    inference(definition_unfolding,[],[f85,f91,f91])).
% 35.42/5.02  
% 35.42/5.02  cnf(c_10,plain,
% 35.42/5.02      ( r1_tarski(k1_xboole_0,X0) ),
% 35.42/5.02      inference(cnf_transformation,[],[f67]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1255,plain,
% 35.42/5.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2,plain,
% 35.42/5.02      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 35.42/5.02      inference(cnf_transformation,[],[f59]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1262,plain,
% 35.42/5.02      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_21,plain,
% 35.42/5.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 35.42/5.02      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 35.42/5.02      inference(cnf_transformation,[],[f108]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1245,plain,
% 35.42/5.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 35.42/5.02      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_14,plain,
% 35.42/5.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.42/5.02      inference(cnf_transformation,[],[f71]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1251,plain,
% 35.42/5.02      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_0,plain,
% 35.42/5.02      ( ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
% 35.42/5.02      | ~ r1_xboole_0(X1,X2) ),
% 35.42/5.02      inference(cnf_transformation,[],[f92]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1264,plain,
% 35.42/5.02      ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.42/5.02      | r1_xboole_0(X1,X2) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3568,plain,
% 35.42/5.02      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_xboole_0
% 35.42/5.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1262,c_1264]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_14447,plain,
% 35.42/5.02      ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1251,c_3568]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_17,plain,
% 35.42/5.02      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 35.42/5.02      inference(cnf_transformation,[],[f102]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3570,plain,
% 35.42/5.02      ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.42/5.02      | r1_xboole_0(X2,X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_1264]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_14453,plain,
% 35.42/5.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 35.42/5.02      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_14447,c_3570]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_14918,plain,
% 35.42/5.02      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 35.42/5.02      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1245,c_14453]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_20170,plain,
% 35.42/5.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 35.42/5.02      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1262,c_14918]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1,plain,
% 35.42/5.02      ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 35.42/5.02      | r1_xboole_0(X0,X1) ),
% 35.42/5.02      inference(cnf_transformation,[],[f93]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1263,plain,
% 35.42/5.02      ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top
% 35.42/5.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3563,plain,
% 35.42/5.02      ( r2_hidden(sK0(X0,X1),k1_setfam_1(k1_enumset1(X1,X1,X0))) = iProver_top
% 35.42/5.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_1263]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4044,plain,
% 35.42/5.02      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3563,c_1264]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_11593,plain,
% 35.42/5.02      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1251,c_4044]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_20183,plain,
% 35.42/5.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.42/5.02      inference(global_propositional_subsumption,
% 35.42/5.02                [status(thm)],
% 35.42/5.02                [c_20170,c_11593]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_26,negated_conjecture,
% 35.42/5.02      ( r1_tarski(sK6,sK7) ),
% 35.42/5.02      inference(cnf_transformation,[],[f88]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1240,plain,
% 35.42/5.02      ( r1_tarski(sK6,sK7) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_6,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 35.42/5.02      inference(cnf_transformation,[],[f94]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1259,plain,
% 35.42/5.02      ( r1_tarski(X0,X1) != iProver_top
% 35.42/5.02      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2935,plain,
% 35.42/5.02      ( r1_tarski(X0,X1) != iProver_top
% 35.42/5.02      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_1259]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_12,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 35.42/5.02      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 35.42/5.02      inference(cnf_transformation,[],[f98]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1253,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4376,plain,
% 35.42/5.02      ( r1_tarski(X0,X1) != iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_2935,c_1253]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_11,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 35.42/5.02      inference(cnf_transformation,[],[f68]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1254,plain,
% 35.42/5.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_16570,plain,
% 35.42/5.02      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_4376,c_1254]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_17535,plain,
% 35.42/5.02      ( k6_subset_1(sK6,sK7) = k1_xboole_0 ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1240,c_16570]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_23,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
% 35.42/5.02      | ~ v1_relat_1(X0)
% 35.42/5.02      | ~ v1_relat_1(X1) ),
% 35.42/5.02      inference(cnf_transformation,[],[f84]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1243,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 35.42/5.02      | v1_relat_1(X0) != iProver_top
% 35.42/5.02      | v1_relat_1(X1) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_17909,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_relat_1(k1_xboole_0)) = iProver_top
% 35.42/5.02      | v1_relat_1(sK7) != iProver_top
% 35.42/5.02      | v1_relat_1(sK6) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17535,c_1243]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_28,negated_conjecture,
% 35.42/5.02      ( v1_relat_1(sK6) ),
% 35.42/5.02      inference(cnf_transformation,[],[f86]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_29,plain,
% 35.42/5.02      ( v1_relat_1(sK6) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_27,negated_conjecture,
% 35.42/5.02      ( v1_relat_1(sK7) ),
% 35.42/5.02      inference(cnf_transformation,[],[f87]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_30,plain,
% 35.42/5.02      ( v1_relat_1(sK7) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_18300,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 35.42/5.02      inference(global_propositional_subsumption,
% 35.42/5.02                [status(thm)],
% 35.42/5.02                [c_17909,c_29,c_30]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_20186,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)),k1_xboole_0) = iProver_top ),
% 35.42/5.02      inference(demodulation,[status(thm)],[c_20183,c_18300]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_20373,plain,
% 35.42/5.02      ( k6_subset_1(k1_relat_1(sK6),k1_relat_1(sK7)) = k1_xboole_0 ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_20186,c_1254]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1239,plain,
% 35.42/5.02      ( v1_relat_1(sK7) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_22,plain,
% 35.42/5.02      ( ~ v1_relat_1(X0)
% 35.42/5.02      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 35.42/5.02      inference(cnf_transformation,[],[f103]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1244,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 35.42/5.02      | v1_relat_1(X0) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3412,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1239,c_1244]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_13,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 35.42/5.02      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 35.42/5.02      inference(cnf_transformation,[],[f99]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1252,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4244,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(X0,k1_relat_1(sK7)),k2_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3412,c_1252]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_20979,plain,
% 35.42/5.02      ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(k1_xboole_0,k2_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_20373,c_4244]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1238,plain,
% 35.42/5.02      ( v1_relat_1(sK6) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3413,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k1_relat_1(sK6),k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1238,c_1244]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_16,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1)
% 35.42/5.02      | ~ r1_tarski(X2,X1)
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 35.42/5.02      inference(cnf_transformation,[],[f101]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1249,plain,
% 35.42/5.02      ( r1_tarski(X0,X1) != iProver_top
% 35.42/5.02      | r1_tarski(X2,X1) != iProver_top
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4006,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK7),X0) = iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3412,c_1249]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_7108,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1259,c_4006]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_141533,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X1,X1,X0))) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),X1) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_7108]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_141599,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k1_relat_1(sK6)))) = iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3413,c_141533]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.42/5.02      inference(cnf_transformation,[],[f62]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1261,plain,
% 35.42/5.02      ( X0 = X1
% 35.42/5.02      | r1_tarski(X0,X1) != iProver_top
% 35.42/5.02      | r1_tarski(X1,X0) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4014,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.42/5.02      | r1_tarski(X0,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X1,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X2,k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1249,c_1261]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_29062,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.42/5.02      | r1_tarski(X1,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X0,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_4014]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_142410,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k1_relat_1(sK6),k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK7)
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_141599,c_29062]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_142415,plain,
% 35.42/5.02      ( k3_relat_1(sK7) = k3_relat_1(sK6)
% 35.42/5.02      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK6)) != iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK7),k1_relat_1(sK6)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(light_normalisation,[status(thm)],[c_142410,c_3413]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_25,negated_conjecture,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
% 35.42/5.02      inference(cnf_transformation,[],[f89]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_32,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_641,plain,( X0 = X0 ),theory(equality) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1373,plain,
% 35.42/5.02      ( k3_relat_1(sK7) = k3_relat_1(sK7) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_641]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f106]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1503,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_5]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1317,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_relat_1(sK6))
% 35.42/5.02      | ~ r1_tarski(k3_relat_1(sK6),X0)
% 35.42/5.02      | k3_relat_1(sK6) = X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_3]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1387,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(X0,X0,X1)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK6))
% 35.42/5.02      | k3_relat_1(sK6) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1317]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1528,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6))
% 35.42/5.02      | k3_relat_1(sK6) = k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1387]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1530,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
% 35.42/5.02      | k3_relat_1(sK6) = k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1528]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_642,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1311,plain,
% 35.42/5.02      ( X0 != X1 | k3_relat_1(sK7) != X1 | k3_relat_1(sK7) = X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_642]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1353,plain,
% 35.42/5.02      ( X0 != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK7) = X0
% 35.42/5.02      | k3_relat_1(sK7) != k3_relat_1(sK7) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1311]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1427,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK7) = k3_tarski(k1_enumset1(X0,X0,X1))
% 35.42/5.02      | k3_tarski(k1_enumset1(X0,X0,X1)) != k3_relat_1(sK7) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1353]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1770,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK7) = k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.42/5.02      | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1427]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_15,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 35.42/5.02      inference(cnf_transformation,[],[f100]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1846,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0))) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_15]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1848,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0))) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1846]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1987,plain,
% 35.42/5.02      ( ~ v1_relat_1(sK7)
% 35.42/5.02      | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_22]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2174,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_relat_1(sK6))
% 35.42/5.02      | ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6))
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_16]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2176,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK6))
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
% 35.42/5.02      | ~ r1_tarski(k1_xboole_0,k3_relat_1(sK6)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_2174]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2509,plain,
% 35.42/5.02      ( r1_tarski(k1_xboole_0,k3_relat_1(sK6)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_10]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_647,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.42/5.02      theory(equality) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1296,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1)
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 35.42/5.02      | k3_relat_1(sK7) != X1
% 35.42/5.02      | k3_relat_1(sK6) != X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_647]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1306,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_relat_1(sK7))
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 35.42/5.02      | k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK6) != X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1296]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3164,plain,
% 35.42/5.02      ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7))
% 35.42/5.02      | k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1306]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3165,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0))
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_3164]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3167,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.42/5.02      | k3_relat_1(sK6) != k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0))
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_3165]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1595,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_relat_1(sK6))
% 35.42/5.02      | ~ r1_tarski(k3_relat_1(sK6),X0)
% 35.42/5.02      | X0 = k3_relat_1(sK6) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_3]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2123,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(X0,X0,X1)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK6))
% 35.42/5.02      | k3_tarski(k1_enumset1(X0,X0,X1)) = k3_relat_1(sK6) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_1595]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_17062,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK6))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) = k3_relat_1(sK6) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_2123]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_17064,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)))
% 35.42/5.02      | ~ r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK6))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) = k3_relat_1(sK6) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_17062]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4378,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.42/5.02      | r1_tarski(X3,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X3)),X1),X2) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1249,c_1253]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_42528,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(X1,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3412,c_4378]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_42541,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(X1,k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(light_normalisation,[status(thm)],[c_42528,c_3412]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_44244,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3413,c_42541]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_4813,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1)
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X2)),k3_relat_1(X3))
% 35.42/5.02      | k3_relat_1(X3) != X1
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X2)) != X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_647]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_10913,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X1)),k3_relat_1(sK7))
% 35.42/5.02      | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X1)) != X0 ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_4813]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_63474,plain,
% 35.42/5.02      ( ~ r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7))
% 35.42/5.02      | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) != k3_relat_1(sK6) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_10913]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_63475,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)) != k3_relat_1(sK6)
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),X0)),k3_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_63474]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_63477,plain,
% 35.42/5.02      ( k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.42/5.02      | k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)) != k3_relat_1(sK6)
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) != iProver_top
% 35.42/5.02      | r1_tarski(k3_tarski(k1_enumset1(k3_relat_1(sK6),k3_relat_1(sK6),k1_xboole_0)),k3_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_63475]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_25810,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))))
% 35.42/5.02      | ~ r1_tarski(k6_subset_1(X0,k1_relat_1(sK7)),k2_relat_1(sK7)) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_13]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_86638,plain,
% 35.42/5.02      ( ~ r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7))
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) ),
% 35.42/5.02      inference(instantiation,[status(thm)],[c_25810]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_86642,plain,
% 35.42/5.02      ( r1_tarski(k6_subset_1(k3_relat_1(sK6),k1_relat_1(sK7)),k2_relat_1(sK7)) != iProver_top
% 35.42/5.02      | r1_tarski(k3_relat_1(sK6),k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_86638]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_9,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1)
% 35.42/5.02      | ~ r1_tarski(X2,X1)
% 35.42/5.02      | r1_tarski(X0,sK2(X0,X1,X2))
% 35.42/5.02      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
% 35.42/5.02      inference(cnf_transformation,[],[f97]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1256,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.42/5.02      | r1_tarski(X0,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X1,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X0,sK2(X0,X2,X1)) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_7,plain,
% 35.42/5.02      ( ~ r1_tarski(X0,X1)
% 35.42/5.02      | ~ r1_tarski(X2,X1)
% 35.42/5.02      | ~ r1_tarski(X1,sK2(X0,X1,X2))
% 35.42/5.02      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
% 35.42/5.02      inference(cnf_transformation,[],[f95]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1258,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.42/5.02      | r1_tarski(X0,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X1,X2) != iProver_top
% 35.42/5.02      | r1_tarski(X2,sK2(X0,X2,X1)) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_6145,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
% 35.42/5.02      | r1_tarski(X0,X0) != iProver_top
% 35.42/5.02      | r1_tarski(X1,X0) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1256,c_1258]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_82,plain,
% 35.42/5.02      ( r1_tarski(X0,X0) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_116198,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
% 35.42/5.02      | r1_tarski(X1,X0) != iProver_top ),
% 35.42/5.02      inference(global_propositional_subsumption,[status(thm)],[c_6145,c_82]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_116212,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(sK7,sK7,sK6)) = sK7 ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1240,c_116198]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_117780,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(sK6,sK6,sK7)) = sK7 ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_17,c_116212]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_24,plain,
% 35.42/5.02      ( ~ v1_relat_1(X0)
% 35.42/5.02      | ~ v1_relat_1(X1)
% 35.42/5.02      | k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 35.42/5.02      inference(cnf_transformation,[],[f104]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1242,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1)))
% 35.42/5.02      | v1_relat_1(X0) != iProver_top
% 35.42/5.02      | v1_relat_1(X1) != iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1779,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k2_relat_1(X0))) = k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,X0)))
% 35.42/5.02      | v1_relat_1(X0) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1238,c_1242]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2196,plain,
% 35.42/5.02      ( k3_tarski(k1_enumset1(k2_relat_1(sK6),k2_relat_1(sK6),k2_relat_1(sK7))) = k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,sK7))) ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1239,c_1779]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_1250,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 35.42/5.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_2198,plain,
% 35.42/5.02      ( r1_tarski(k2_relat_1(sK6),k2_relat_1(k3_tarski(k1_enumset1(sK6,sK6,sK7)))) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_2196,c_1250]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_117963,plain,
% 35.42/5.02      ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(demodulation,[status(thm)],[c_117780,c_2198]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_3661,plain,
% 35.42/5.02      ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
% 35.42/5.02      | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_3412,c_1259]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_119916,plain,
% 35.42/5.02      ( r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7)) = iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_117963,c_3661]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_142964,plain,
% 35.42/5.02      ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(global_propositional_subsumption,
% 35.42/5.02                [status(thm)],
% 35.42/5.02                [c_142415,c_27,c_32,c_1373,c_1503,c_1530,c_1770,c_1848,
% 35.42/5.02                 c_1987,c_2176,c_2509,c_3167,c_17064,c_44244,c_63477,c_86642,
% 35.42/5.02                 c_119916]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_142968,plain,
% 35.42/5.02      ( r1_tarski(k1_xboole_0,k2_relat_1(sK7)) != iProver_top ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_20979,c_142964]) ).
% 35.42/5.02  
% 35.42/5.02  cnf(c_146008,plain,
% 35.42/5.02      ( $false ),
% 35.42/5.02      inference(superposition,[status(thm)],[c_1255,c_142968]) ).
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 35.42/5.02  
% 35.42/5.02  ------                               Statistics
% 35.42/5.02  
% 35.42/5.02  ------ General
% 35.42/5.02  
% 35.42/5.02  abstr_ref_over_cycles:                  0
% 35.42/5.02  abstr_ref_under_cycles:                 0
% 35.42/5.02  gc_basic_clause_elim:                   0
% 35.42/5.02  forced_gc_time:                         0
% 35.42/5.02  parsing_time:                           0.009
% 35.42/5.02  unif_index_cands_time:                  0.
% 35.42/5.02  unif_index_add_time:                    0.
% 35.42/5.02  orderings_time:                         0.
% 35.42/5.02  out_proof_time:                         0.03
% 35.42/5.02  total_time:                             4.27
% 35.42/5.02  num_of_symbols:                         52
% 35.42/5.02  num_of_terms:                           125710
% 35.42/5.02  
% 35.42/5.02  ------ Preprocessing
% 35.42/5.02  
% 35.42/5.02  num_of_splits:                          0
% 35.42/5.02  num_of_split_atoms:                     0
% 35.42/5.02  num_of_reused_defs:                     0
% 35.42/5.02  num_eq_ax_congr_red:                    39
% 35.42/5.02  num_of_sem_filtered_clauses:            1
% 35.42/5.02  num_of_subtypes:                        0
% 35.42/5.02  monotx_restored_types:                  0
% 35.42/5.02  sat_num_of_epr_types:                   0
% 35.42/5.02  sat_num_of_non_cyclic_types:            0
% 35.42/5.02  sat_guarded_non_collapsed_types:        0
% 35.42/5.02  num_pure_diseq_elim:                    0
% 35.42/5.02  simp_replaced_by:                       0
% 35.42/5.02  res_preprocessed:                       141
% 35.42/5.02  prep_upred:                             0
% 35.42/5.02  prep_unflattend:                        8
% 35.42/5.02  smt_new_axioms:                         0
% 35.42/5.02  pred_elim_cands:                        4
% 35.42/5.02  pred_elim:                              0
% 35.42/5.02  pred_elim_cl:                           0
% 35.42/5.02  pred_elim_cycles:                       2
% 35.42/5.02  merged_defs:                            8
% 35.42/5.02  merged_defs_ncl:                        0
% 35.42/5.02  bin_hyper_res:                          8
% 35.42/5.02  prep_cycles:                            4
% 35.42/5.02  pred_elim_time:                         0.001
% 35.42/5.02  splitting_time:                         0.
% 35.42/5.02  sem_filter_time:                        0.
% 35.42/5.02  monotx_time:                            0.
% 35.42/5.02  subtype_inf_time:                       0.
% 35.42/5.02  
% 35.42/5.02  ------ Problem properties
% 35.42/5.02  
% 35.42/5.02  clauses:                                28
% 35.42/5.02  conjectures:                            4
% 35.42/5.02  epr:                                    8
% 35.42/5.02  horn:                                   23
% 35.42/5.02  ground:                                 4
% 35.42/5.02  unary:                                  9
% 35.42/5.02  binary:                                 10
% 35.42/5.02  lits:                                   59
% 35.42/5.02  lits_eq:                                11
% 35.42/5.02  fd_pure:                                0
% 35.42/5.02  fd_pseudo:                              0
% 35.42/5.02  fd_cond:                                2
% 35.42/5.02  fd_pseudo_cond:                         6
% 35.42/5.02  ac_symbols:                             0
% 35.42/5.02  
% 35.42/5.02  ------ Propositional Solver
% 35.42/5.02  
% 35.42/5.02  prop_solver_calls:                      51
% 35.42/5.02  prop_fast_solver_calls:                 2150
% 35.42/5.02  smt_solver_calls:                       0
% 35.42/5.02  smt_fast_solver_calls:                  0
% 35.42/5.02  prop_num_of_clauses:                    50636
% 35.42/5.02  prop_preprocess_simplified:             65331
% 35.42/5.02  prop_fo_subsumed:                       25
% 35.42/5.02  prop_solver_time:                       0.
% 35.42/5.02  smt_solver_time:                        0.
% 35.42/5.02  smt_fast_solver_time:                   0.
% 35.42/5.02  prop_fast_solver_time:                  0.
% 35.42/5.02  prop_unsat_core_time:                   0.
% 35.42/5.02  
% 35.42/5.02  ------ QBF
% 35.42/5.02  
% 35.42/5.02  qbf_q_res:                              0
% 35.42/5.02  qbf_num_tautologies:                    0
% 35.42/5.02  qbf_prep_cycles:                        0
% 35.42/5.02  
% 35.42/5.02  ------ BMC1
% 35.42/5.02  
% 35.42/5.02  bmc1_current_bound:                     -1
% 35.42/5.02  bmc1_last_solved_bound:                 -1
% 35.42/5.02  bmc1_unsat_core_size:                   -1
% 35.42/5.02  bmc1_unsat_core_parents_size:           -1
% 35.42/5.02  bmc1_merge_next_fun:                    0
% 35.42/5.02  bmc1_unsat_core_clauses_time:           0.
% 35.42/5.02  
% 35.42/5.02  ------ Instantiation
% 35.42/5.02  
% 35.42/5.02  inst_num_of_clauses:                    2559
% 35.42/5.02  inst_num_in_passive:                    975
% 35.42/5.02  inst_num_in_active:                     3215
% 35.42/5.02  inst_num_in_unprocessed:                681
% 35.42/5.02  inst_num_of_loops:                      4389
% 35.42/5.02  inst_num_of_learning_restarts:          1
% 35.42/5.02  inst_num_moves_active_passive:          1168
% 35.42/5.02  inst_lit_activity:                      0
% 35.42/5.02  inst_lit_activity_moves:                0
% 35.42/5.02  inst_num_tautologies:                   0
% 35.42/5.02  inst_num_prop_implied:                  0
% 35.42/5.02  inst_num_existing_simplified:           0
% 35.42/5.02  inst_num_eq_res_simplified:             0
% 35.42/5.02  inst_num_child_elim:                    0
% 35.42/5.02  inst_num_of_dismatching_blockings:      19054
% 35.42/5.02  inst_num_of_non_proper_insts:           15030
% 35.42/5.02  inst_num_of_duplicates:                 0
% 35.42/5.02  inst_inst_num_from_inst_to_res:         0
% 35.42/5.02  inst_dismatching_checking_time:         0.
% 35.42/5.02  
% 35.42/5.02  ------ Resolution
% 35.42/5.02  
% 35.42/5.02  res_num_of_clauses:                     42
% 35.42/5.02  res_num_in_passive:                     42
% 35.42/5.02  res_num_in_active:                      0
% 35.42/5.02  res_num_of_loops:                       145
% 35.42/5.02  res_forward_subset_subsumed:            2392
% 35.42/5.02  res_backward_subset_subsumed:           38
% 35.42/5.02  res_forward_subsumed:                   0
% 35.42/5.02  res_backward_subsumed:                  0
% 35.42/5.02  res_forward_subsumption_resolution:     0
% 35.42/5.02  res_backward_subsumption_resolution:    0
% 35.42/5.02  res_clause_to_clause_subsumption:       69461
% 35.42/5.02  res_orphan_elimination:                 0
% 35.42/5.02  res_tautology_del:                      1084
% 35.42/5.02  res_num_eq_res_simplified:              0
% 35.42/5.02  res_num_sel_changes:                    0
% 35.42/5.02  res_moves_from_active_to_pass:          0
% 35.42/5.02  
% 35.42/5.02  ------ Superposition
% 35.42/5.02  
% 35.42/5.02  sup_time_total:                         0.
% 35.42/5.02  sup_time_generating:                    0.
% 35.42/5.02  sup_time_sim_full:                      0.
% 35.42/5.02  sup_time_sim_immed:                     0.
% 35.42/5.02  
% 35.42/5.02  sup_num_of_clauses:                     8792
% 35.42/5.02  sup_num_in_active:                      595
% 35.42/5.02  sup_num_in_passive:                     8197
% 35.42/5.02  sup_num_of_loops:                       876
% 35.42/5.02  sup_fw_superposition:                   11495
% 35.42/5.02  sup_bw_superposition:                   12527
% 35.42/5.02  sup_immediate_simplified:               6308
% 35.42/5.02  sup_given_eliminated:                   8
% 35.42/5.02  comparisons_done:                       0
% 35.42/5.02  comparisons_avoided:                    4
% 35.42/5.02  
% 35.42/5.02  ------ Simplifications
% 35.42/5.02  
% 35.42/5.02  
% 35.42/5.02  sim_fw_subset_subsumed:                 619
% 35.42/5.02  sim_bw_subset_subsumed:                 88
% 35.42/5.02  sim_fw_subsumed:                        2567
% 35.42/5.02  sim_bw_subsumed:                        123
% 35.42/5.02  sim_fw_subsumption_res:                 0
% 35.42/5.02  sim_bw_subsumption_res:                 0
% 35.42/5.02  sim_tautology_del:                      83
% 35.42/5.02  sim_eq_tautology_del:                   166
% 35.42/5.02  sim_eq_res_simp:                        0
% 35.42/5.02  sim_fw_demodulated:                     2110
% 35.42/5.02  sim_bw_demodulated:                     310
% 35.42/5.02  sim_light_normalised:                   1453
% 35.42/5.02  sim_joinable_taut:                      0
% 35.42/5.02  sim_joinable_simp:                      0
% 35.42/5.02  sim_ac_normalised:                      0
% 35.42/5.02  sim_smt_subsumption:                    0
% 35.42/5.02  
%------------------------------------------------------------------------------
