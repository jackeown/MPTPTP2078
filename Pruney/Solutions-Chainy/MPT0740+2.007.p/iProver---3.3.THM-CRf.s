%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:32 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 109 expanded)
%              Number of clauses        :   37 (  38 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 ( 332 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f39,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK2))
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v3_ordinal1(k3_tarski(sK2))
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f31])).

fof(f46,plain,(
    ~ v3_ordinal1(k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_529,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | r1_tarski(sK1(k3_tarski(sK2)),X0)
    | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_636,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_639,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_438,plain,
    ( r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | v1_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(sK1(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_439,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(sK2))
    | v1_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_333,plain,
    ( ~ r2_hidden(k3_tarski(sK2),X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_388,plain,
    ( ~ r2_hidden(k3_tarski(sK2),k1_ordinal1(X0))
    | ~ v3_ordinal1(k1_ordinal1(X0))
    | v3_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_394,plain,
    ( ~ r2_hidden(k3_tarski(sK2),k1_ordinal1(sK2))
    | ~ v3_ordinal1(k1_ordinal1(sK2))
    | v3_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | ~ v1_ordinal1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_81,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r1_tarski(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_82,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X2) ),
    inference(renaming,[status(thm)],[c_81])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(X1,k1_ordinal1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ v3_ordinal1(k1_ordinal1(X0))
    | ~ v1_ordinal1(X1) ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_387,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(k3_tarski(sK2),k1_ordinal1(X0))
    | ~ r1_tarski(k3_tarski(sK2),X0)
    | ~ v3_ordinal1(k1_ordinal1(X0))
    | ~ v1_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_390,plain,
    ( r2_hidden(k3_tarski(sK2),k1_ordinal1(sK2))
    | ~ r2_hidden(sK2,k1_ordinal1(sK2))
    | ~ r1_tarski(k3_tarski(sK2),sK2)
    | ~ v3_ordinal1(k1_ordinal1(sK2))
    | ~ v1_ordinal1(k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_363,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(sK0(X0,X1),X0)
    | ~ v1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_375,plain,
    ( ~ r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK0(sK2,sK2),sK2)
    | ~ v1_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_338,plain,
    ( ~ r1_tarski(k3_tarski(X0),X1)
    | r1_tarski(k3_tarski(k3_tarski(X0)),k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_340,plain,
    ( r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(sK2))
    | ~ r1_tarski(k3_tarski(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_0,plain,
    ( ~ r1_tarski(sK0(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_46,plain,
    ( ~ r1_tarski(sK0(sK2,sK2),sK2)
    | r1_tarski(k3_tarski(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_43,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(k3_tarski(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_34,plain,
    ( ~ v3_ordinal1(sK2)
    | v1_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( r2_hidden(sK2,k1_ordinal1(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( v3_ordinal1(k1_ordinal1(sK2))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_639,c_438,c_439,c_394,c_390,c_375,c_340,c_46,c_43,c_34,c_22,c_17,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:36:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 0.53/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.53/1.01  
% 0.53/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.53/1.01  
% 0.53/1.01  ------  iProver source info
% 0.53/1.01  
% 0.53/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.53/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.53/1.01  git: non_committed_changes: false
% 0.53/1.01  git: last_make_outside_of_git: false
% 0.53/1.01  
% 0.53/1.01  ------ 
% 0.53/1.01  
% 0.53/1.01  ------ Input Options
% 0.53/1.01  
% 0.53/1.01  --out_options                           all
% 0.53/1.01  --tptp_safe_out                         true
% 0.53/1.01  --problem_path                          ""
% 0.53/1.01  --include_path                          ""
% 0.53/1.01  --clausifier                            res/vclausify_rel
% 0.53/1.01  --clausifier_options                    --mode clausify
% 0.53/1.01  --stdin                                 false
% 0.53/1.01  --stats_out                             all
% 0.53/1.01  
% 0.53/1.01  ------ General Options
% 0.53/1.01  
% 0.53/1.01  --fof                                   false
% 0.53/1.01  --time_out_real                         305.
% 0.53/1.01  --time_out_virtual                      -1.
% 0.53/1.01  --symbol_type_check                     false
% 0.53/1.01  --clausify_out                          false
% 0.53/1.01  --sig_cnt_out                           false
% 0.53/1.01  --trig_cnt_out                          false
% 0.53/1.01  --trig_cnt_out_tolerance                1.
% 0.53/1.01  --trig_cnt_out_sk_spl                   false
% 0.53/1.01  --abstr_cl_out                          false
% 0.53/1.01  
% 0.53/1.01  ------ Global Options
% 0.53/1.01  
% 0.53/1.01  --schedule                              default
% 0.53/1.01  --add_important_lit                     false
% 0.53/1.01  --prop_solver_per_cl                    1000
% 0.53/1.01  --min_unsat_core                        false
% 0.53/1.01  --soft_assumptions                      false
% 0.53/1.01  --soft_lemma_size                       3
% 0.53/1.01  --prop_impl_unit_size                   0
% 0.53/1.01  --prop_impl_unit                        []
% 0.53/1.01  --share_sel_clauses                     true
% 0.53/1.01  --reset_solvers                         false
% 0.53/1.01  --bc_imp_inh                            [conj_cone]
% 0.53/1.01  --conj_cone_tolerance                   3.
% 0.53/1.01  --extra_neg_conj                        none
% 0.53/1.01  --large_theory_mode                     true
% 0.53/1.01  --prolific_symb_bound                   200
% 0.53/1.01  --lt_threshold                          2000
% 0.53/1.01  --clause_weak_htbl                      true
% 0.53/1.01  --gc_record_bc_elim                     false
% 0.53/1.01  
% 0.53/1.01  ------ Preprocessing Options
% 0.53/1.01  
% 0.53/1.01  --preprocessing_flag                    true
% 0.53/1.01  --time_out_prep_mult                    0.1
% 0.53/1.01  --splitting_mode                        input
% 0.53/1.01  --splitting_grd                         true
% 0.53/1.01  --splitting_cvd                         false
% 0.53/1.01  --splitting_cvd_svl                     false
% 0.53/1.01  --splitting_nvd                         32
% 0.53/1.01  --sub_typing                            true
% 0.53/1.01  --prep_gs_sim                           true
% 0.53/1.01  --prep_unflatten                        true
% 0.53/1.01  --prep_res_sim                          true
% 0.53/1.01  --prep_upred                            true
% 0.53/1.01  --prep_sem_filter                       exhaustive
% 0.53/1.01  --prep_sem_filter_out                   false
% 0.53/1.01  --pred_elim                             true
% 0.53/1.01  --res_sim_input                         true
% 0.53/1.01  --eq_ax_congr_red                       true
% 0.53/1.01  --pure_diseq_elim                       true
% 0.53/1.01  --brand_transform                       false
% 0.53/1.01  --non_eq_to_eq                          false
% 0.53/1.01  --prep_def_merge                        true
% 0.53/1.01  --prep_def_merge_prop_impl              false
% 0.53/1.01  --prep_def_merge_mbd                    true
% 0.53/1.01  --prep_def_merge_tr_red                 false
% 0.53/1.01  --prep_def_merge_tr_cl                  false
% 0.53/1.01  --smt_preprocessing                     true
% 0.53/1.01  --smt_ac_axioms                         fast
% 0.53/1.01  --preprocessed_out                      false
% 0.53/1.01  --preprocessed_stats                    false
% 0.53/1.01  
% 0.53/1.01  ------ Abstraction refinement Options
% 0.53/1.01  
% 0.53/1.01  --abstr_ref                             []
% 0.53/1.01  --abstr_ref_prep                        false
% 0.53/1.01  --abstr_ref_until_sat                   false
% 0.53/1.01  --abstr_ref_sig_restrict                funpre
% 0.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.53/1.01  --abstr_ref_under                       []
% 0.53/1.01  
% 0.53/1.01  ------ SAT Options
% 0.53/1.01  
% 0.53/1.01  --sat_mode                              false
% 0.53/1.01  --sat_fm_restart_options                ""
% 0.53/1.01  --sat_gr_def                            false
% 0.53/1.01  --sat_epr_types                         true
% 0.53/1.01  --sat_non_cyclic_types                  false
% 0.53/1.01  --sat_finite_models                     false
% 0.53/1.01  --sat_fm_lemmas                         false
% 0.53/1.01  --sat_fm_prep                           false
% 0.53/1.01  --sat_fm_uc_incr                        true
% 0.53/1.01  --sat_out_model                         small
% 0.53/1.01  --sat_out_clauses                       false
% 0.53/1.01  
% 0.53/1.01  ------ QBF Options
% 0.53/1.01  
% 0.53/1.01  --qbf_mode                              false
% 0.53/1.01  --qbf_elim_univ                         false
% 0.53/1.01  --qbf_dom_inst                          none
% 0.53/1.01  --qbf_dom_pre_inst                      false
% 0.53/1.01  --qbf_sk_in                             false
% 0.53/1.01  --qbf_pred_elim                         true
% 0.53/1.01  --qbf_split                             512
% 0.53/1.01  
% 0.53/1.01  ------ BMC1 Options
% 0.53/1.01  
% 0.53/1.01  --bmc1_incremental                      false
% 0.53/1.01  --bmc1_axioms                           reachable_all
% 0.53/1.01  --bmc1_min_bound                        0
% 0.53/1.01  --bmc1_max_bound                        -1
% 0.53/1.01  --bmc1_max_bound_default                -1
% 0.53/1.01  --bmc1_symbol_reachability              true
% 0.53/1.01  --bmc1_property_lemmas                  false
% 0.53/1.01  --bmc1_k_induction                      false
% 0.53/1.01  --bmc1_non_equiv_states                 false
% 0.53/1.01  --bmc1_deadlock                         false
% 0.53/1.01  --bmc1_ucm                              false
% 0.53/1.01  --bmc1_add_unsat_core                   none
% 0.53/1.01  --bmc1_unsat_core_children              false
% 0.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.53/1.01  --bmc1_out_stat                         full
% 0.53/1.01  --bmc1_ground_init                      false
% 0.53/1.01  --bmc1_pre_inst_next_state              false
% 0.53/1.01  --bmc1_pre_inst_state                   false
% 0.53/1.01  --bmc1_pre_inst_reach_state             false
% 0.53/1.01  --bmc1_out_unsat_core                   false
% 0.53/1.01  --bmc1_aig_witness_out                  false
% 0.53/1.01  --bmc1_verbose                          false
% 0.53/1.01  --bmc1_dump_clauses_tptp                false
% 0.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.53/1.01  --bmc1_dump_file                        -
% 0.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.53/1.01  --bmc1_ucm_extend_mode                  1
% 0.53/1.01  --bmc1_ucm_init_mode                    2
% 0.53/1.01  --bmc1_ucm_cone_mode                    none
% 0.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.53/1.01  --bmc1_ucm_relax_model                  4
% 0.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.53/1.01  --bmc1_ucm_layered_model                none
% 0.53/1.01  --bmc1_ucm_max_lemma_size               10
% 0.53/1.01  
% 0.53/1.01  ------ AIG Options
% 0.53/1.01  
% 0.53/1.01  --aig_mode                              false
% 0.53/1.01  
% 0.53/1.01  ------ Instantiation Options
% 0.53/1.01  
% 0.53/1.01  --instantiation_flag                    true
% 0.53/1.01  --inst_sos_flag                         false
% 0.53/1.01  --inst_sos_phase                        true
% 0.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.53/1.01  --inst_lit_sel_side                     num_symb
% 0.53/1.01  --inst_solver_per_active                1400
% 0.53/1.01  --inst_solver_calls_frac                1.
% 0.53/1.01  --inst_passive_queue_type               priority_queues
% 0.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.53/1.01  --inst_passive_queues_freq              [25;2]
% 0.53/1.01  --inst_dismatching                      true
% 0.53/1.01  --inst_eager_unprocessed_to_passive     true
% 0.53/1.01  --inst_prop_sim_given                   true
% 0.53/1.01  --inst_prop_sim_new                     false
% 0.53/1.01  --inst_subs_new                         false
% 0.53/1.01  --inst_eq_res_simp                      false
% 0.53/1.01  --inst_subs_given                       false
% 0.53/1.01  --inst_orphan_elimination               true
% 0.53/1.01  --inst_learning_loop_flag               true
% 0.53/1.01  --inst_learning_start                   3000
% 0.53/1.01  --inst_learning_factor                  2
% 0.53/1.01  --inst_start_prop_sim_after_learn       3
% 0.53/1.01  --inst_sel_renew                        solver
% 0.53/1.01  --inst_lit_activity_flag                true
% 0.53/1.01  --inst_restr_to_given                   false
% 0.53/1.01  --inst_activity_threshold               500
% 0.53/1.01  --inst_out_proof                        true
% 0.53/1.01  
% 0.53/1.01  ------ Resolution Options
% 0.53/1.01  
% 0.53/1.01  --resolution_flag                       true
% 0.53/1.01  --res_lit_sel                           adaptive
% 0.53/1.01  --res_lit_sel_side                      none
% 0.53/1.01  --res_ordering                          kbo
% 0.53/1.01  --res_to_prop_solver                    active
% 0.53/1.01  --res_prop_simpl_new                    false
% 0.53/1.01  --res_prop_simpl_given                  true
% 0.53/1.01  --res_passive_queue_type                priority_queues
% 0.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.53/1.01  --res_passive_queues_freq               [15;5]
% 0.53/1.01  --res_forward_subs                      full
% 0.53/1.01  --res_backward_subs                     full
% 0.53/1.01  --res_forward_subs_resolution           true
% 0.53/1.01  --res_backward_subs_resolution          true
% 0.53/1.01  --res_orphan_elimination                true
% 0.53/1.01  --res_time_limit                        2.
% 0.53/1.01  --res_out_proof                         true
% 0.53/1.01  
% 0.53/1.01  ------ Superposition Options
% 0.53/1.01  
% 0.53/1.01  --superposition_flag                    true
% 0.53/1.01  --sup_passive_queue_type                priority_queues
% 0.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.53/1.01  --demod_completeness_check              fast
% 0.53/1.01  --demod_use_ground                      true
% 0.53/1.01  --sup_to_prop_solver                    passive
% 0.53/1.01  --sup_prop_simpl_new                    true
% 0.53/1.01  --sup_prop_simpl_given                  true
% 0.53/1.01  --sup_fun_splitting                     false
% 0.53/1.01  --sup_smt_interval                      50000
% 0.53/1.01  
% 0.53/1.01  ------ Superposition Simplification Setup
% 0.53/1.01  
% 0.53/1.01  --sup_indices_passive                   []
% 0.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_full_bw                           [BwDemod]
% 0.53/1.01  --sup_immed_triv                        [TrivRules]
% 0.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_immed_bw_main                     []
% 0.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.53/1.01  
% 0.53/1.01  ------ Combination Options
% 0.53/1.01  
% 0.53/1.01  --comb_res_mult                         3
% 0.53/1.01  --comb_sup_mult                         2
% 0.53/1.01  --comb_inst_mult                        10
% 0.53/1.01  
% 0.53/1.01  ------ Debug Options
% 0.53/1.01  
% 0.53/1.01  --dbg_backtrace                         false
% 0.53/1.01  --dbg_dump_prop_clauses                 false
% 0.53/1.01  --dbg_dump_prop_clauses_file            -
% 0.53/1.01  --dbg_out_stat                          false
% 0.53/1.01  ------ Parsing...
% 0.53/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.53/1.01  
% 0.53/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.53/1.01  
% 0.53/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.53/1.01  ------ Proving...
% 0.53/1.01  ------ Problem Properties 
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  clauses                                 14
% 0.53/1.01  conjectures                             2
% 0.53/1.01  EPR                                     5
% 0.53/1.01  Horn                                    12
% 0.53/1.01  unary                                   3
% 0.53/1.01  binary                                  7
% 0.53/1.01  lits                                    31
% 0.53/1.01  lits eq                                 0
% 0.53/1.01  fd_pure                                 0
% 0.53/1.01  fd_pseudo                               0
% 0.53/1.01  fd_cond                                 0
% 0.53/1.01  fd_pseudo_cond                          0
% 0.53/1.01  AC symbols                              0
% 0.53/1.01  
% 0.53/1.01  ------ Schedule dynamic 5 is on 
% 0.53/1.01  
% 0.53/1.01  ------ no equalities: superposition off 
% 0.53/1.01  
% 0.53/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  ------ 
% 0.53/1.01  Current options:
% 0.53/1.01  ------ 
% 0.53/1.01  
% 0.53/1.01  ------ Input Options
% 0.53/1.01  
% 0.53/1.01  --out_options                           all
% 0.53/1.01  --tptp_safe_out                         true
% 0.53/1.01  --problem_path                          ""
% 0.53/1.01  --include_path                          ""
% 0.53/1.01  --clausifier                            res/vclausify_rel
% 0.53/1.01  --clausifier_options                    --mode clausify
% 0.53/1.01  --stdin                                 false
% 0.53/1.01  --stats_out                             all
% 0.53/1.01  
% 0.53/1.01  ------ General Options
% 0.53/1.01  
% 0.53/1.01  --fof                                   false
% 0.53/1.01  --time_out_real                         305.
% 0.53/1.01  --time_out_virtual                      -1.
% 0.53/1.01  --symbol_type_check                     false
% 0.53/1.01  --clausify_out                          false
% 0.53/1.01  --sig_cnt_out                           false
% 0.53/1.01  --trig_cnt_out                          false
% 0.53/1.01  --trig_cnt_out_tolerance                1.
% 0.53/1.01  --trig_cnt_out_sk_spl                   false
% 0.53/1.01  --abstr_cl_out                          false
% 0.53/1.01  
% 0.53/1.01  ------ Global Options
% 0.53/1.01  
% 0.53/1.01  --schedule                              default
% 0.53/1.01  --add_important_lit                     false
% 0.53/1.01  --prop_solver_per_cl                    1000
% 0.53/1.01  --min_unsat_core                        false
% 0.53/1.01  --soft_assumptions                      false
% 0.53/1.01  --soft_lemma_size                       3
% 0.53/1.01  --prop_impl_unit_size                   0
% 0.53/1.01  --prop_impl_unit                        []
% 0.53/1.01  --share_sel_clauses                     true
% 0.53/1.01  --reset_solvers                         false
% 0.53/1.01  --bc_imp_inh                            [conj_cone]
% 0.53/1.01  --conj_cone_tolerance                   3.
% 0.53/1.01  --extra_neg_conj                        none
% 0.53/1.01  --large_theory_mode                     true
% 0.53/1.01  --prolific_symb_bound                   200
% 0.53/1.01  --lt_threshold                          2000
% 0.53/1.01  --clause_weak_htbl                      true
% 0.53/1.01  --gc_record_bc_elim                     false
% 0.53/1.01  
% 0.53/1.01  ------ Preprocessing Options
% 0.53/1.01  
% 0.53/1.01  --preprocessing_flag                    true
% 0.53/1.01  --time_out_prep_mult                    0.1
% 0.53/1.01  --splitting_mode                        input
% 0.53/1.01  --splitting_grd                         true
% 0.53/1.01  --splitting_cvd                         false
% 0.53/1.01  --splitting_cvd_svl                     false
% 0.53/1.01  --splitting_nvd                         32
% 0.53/1.01  --sub_typing                            true
% 0.53/1.01  --prep_gs_sim                           true
% 0.53/1.01  --prep_unflatten                        true
% 0.53/1.01  --prep_res_sim                          true
% 0.53/1.01  --prep_upred                            true
% 0.53/1.01  --prep_sem_filter                       exhaustive
% 0.53/1.01  --prep_sem_filter_out                   false
% 0.53/1.01  --pred_elim                             true
% 0.53/1.01  --res_sim_input                         true
% 0.53/1.01  --eq_ax_congr_red                       true
% 0.53/1.01  --pure_diseq_elim                       true
% 0.53/1.01  --brand_transform                       false
% 0.53/1.01  --non_eq_to_eq                          false
% 0.53/1.01  --prep_def_merge                        true
% 0.53/1.01  --prep_def_merge_prop_impl              false
% 0.53/1.01  --prep_def_merge_mbd                    true
% 0.53/1.01  --prep_def_merge_tr_red                 false
% 0.53/1.01  --prep_def_merge_tr_cl                  false
% 0.53/1.01  --smt_preprocessing                     true
% 0.53/1.01  --smt_ac_axioms                         fast
% 0.53/1.01  --preprocessed_out                      false
% 0.53/1.01  --preprocessed_stats                    false
% 0.53/1.01  
% 0.53/1.01  ------ Abstraction refinement Options
% 0.53/1.01  
% 0.53/1.01  --abstr_ref                             []
% 0.53/1.01  --abstr_ref_prep                        false
% 0.53/1.01  --abstr_ref_until_sat                   false
% 0.53/1.01  --abstr_ref_sig_restrict                funpre
% 0.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.53/1.01  --abstr_ref_under                       []
% 0.53/1.01  
% 0.53/1.01  ------ SAT Options
% 0.53/1.01  
% 0.53/1.01  --sat_mode                              false
% 0.53/1.01  --sat_fm_restart_options                ""
% 0.53/1.01  --sat_gr_def                            false
% 0.53/1.01  --sat_epr_types                         true
% 0.53/1.01  --sat_non_cyclic_types                  false
% 0.53/1.01  --sat_finite_models                     false
% 0.53/1.01  --sat_fm_lemmas                         false
% 0.53/1.01  --sat_fm_prep                           false
% 0.53/1.01  --sat_fm_uc_incr                        true
% 0.53/1.01  --sat_out_model                         small
% 0.53/1.01  --sat_out_clauses                       false
% 0.53/1.01  
% 0.53/1.01  ------ QBF Options
% 0.53/1.01  
% 0.53/1.01  --qbf_mode                              false
% 0.53/1.01  --qbf_elim_univ                         false
% 0.53/1.01  --qbf_dom_inst                          none
% 0.53/1.01  --qbf_dom_pre_inst                      false
% 0.53/1.01  --qbf_sk_in                             false
% 0.53/1.01  --qbf_pred_elim                         true
% 0.53/1.01  --qbf_split                             512
% 0.53/1.01  
% 0.53/1.01  ------ BMC1 Options
% 0.53/1.01  
% 0.53/1.01  --bmc1_incremental                      false
% 0.53/1.01  --bmc1_axioms                           reachable_all
% 0.53/1.01  --bmc1_min_bound                        0
% 0.53/1.01  --bmc1_max_bound                        -1
% 0.53/1.01  --bmc1_max_bound_default                -1
% 0.53/1.01  --bmc1_symbol_reachability              true
% 0.53/1.01  --bmc1_property_lemmas                  false
% 0.53/1.01  --bmc1_k_induction                      false
% 0.53/1.01  --bmc1_non_equiv_states                 false
% 0.53/1.01  --bmc1_deadlock                         false
% 0.53/1.01  --bmc1_ucm                              false
% 0.53/1.01  --bmc1_add_unsat_core                   none
% 0.53/1.01  --bmc1_unsat_core_children              false
% 0.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.53/1.01  --bmc1_out_stat                         full
% 0.53/1.01  --bmc1_ground_init                      false
% 0.53/1.01  --bmc1_pre_inst_next_state              false
% 0.53/1.01  --bmc1_pre_inst_state                   false
% 0.53/1.01  --bmc1_pre_inst_reach_state             false
% 0.53/1.01  --bmc1_out_unsat_core                   false
% 0.53/1.01  --bmc1_aig_witness_out                  false
% 0.53/1.01  --bmc1_verbose                          false
% 0.53/1.01  --bmc1_dump_clauses_tptp                false
% 0.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.53/1.01  --bmc1_dump_file                        -
% 0.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.53/1.01  --bmc1_ucm_extend_mode                  1
% 0.53/1.01  --bmc1_ucm_init_mode                    2
% 0.53/1.01  --bmc1_ucm_cone_mode                    none
% 0.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.53/1.01  --bmc1_ucm_relax_model                  4
% 0.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.53/1.01  --bmc1_ucm_layered_model                none
% 0.53/1.01  --bmc1_ucm_max_lemma_size               10
% 0.53/1.01  
% 0.53/1.01  ------ AIG Options
% 0.53/1.01  
% 0.53/1.01  --aig_mode                              false
% 0.53/1.01  
% 0.53/1.01  ------ Instantiation Options
% 0.53/1.01  
% 0.53/1.01  --instantiation_flag                    true
% 0.53/1.01  --inst_sos_flag                         false
% 0.53/1.01  --inst_sos_phase                        true
% 0.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.53/1.01  --inst_lit_sel_side                     none
% 0.53/1.01  --inst_solver_per_active                1400
% 0.53/1.01  --inst_solver_calls_frac                1.
% 0.53/1.01  --inst_passive_queue_type               priority_queues
% 0.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.53/1.01  --inst_passive_queues_freq              [25;2]
% 0.53/1.01  --inst_dismatching                      true
% 0.53/1.01  --inst_eager_unprocessed_to_passive     true
% 0.53/1.01  --inst_prop_sim_given                   true
% 0.53/1.01  --inst_prop_sim_new                     false
% 0.53/1.01  --inst_subs_new                         false
% 0.53/1.01  --inst_eq_res_simp                      false
% 0.53/1.01  --inst_subs_given                       false
% 0.53/1.01  --inst_orphan_elimination               true
% 0.53/1.01  --inst_learning_loop_flag               true
% 0.53/1.01  --inst_learning_start                   3000
% 0.53/1.01  --inst_learning_factor                  2
% 0.53/1.01  --inst_start_prop_sim_after_learn       3
% 0.53/1.01  --inst_sel_renew                        solver
% 0.53/1.01  --inst_lit_activity_flag                true
% 0.53/1.01  --inst_restr_to_given                   false
% 0.53/1.01  --inst_activity_threshold               500
% 0.53/1.01  --inst_out_proof                        true
% 0.53/1.01  
% 0.53/1.01  ------ Resolution Options
% 0.53/1.01  
% 0.53/1.01  --resolution_flag                       false
% 0.53/1.01  --res_lit_sel                           adaptive
% 0.53/1.01  --res_lit_sel_side                      none
% 0.53/1.01  --res_ordering                          kbo
% 0.53/1.01  --res_to_prop_solver                    active
% 0.53/1.01  --res_prop_simpl_new                    false
% 0.53/1.01  --res_prop_simpl_given                  true
% 0.53/1.01  --res_passive_queue_type                priority_queues
% 0.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.53/1.01  --res_passive_queues_freq               [15;5]
% 0.53/1.01  --res_forward_subs                      full
% 0.53/1.01  --res_backward_subs                     full
% 0.53/1.01  --res_forward_subs_resolution           true
% 0.53/1.01  --res_backward_subs_resolution          true
% 0.53/1.01  --res_orphan_elimination                true
% 0.53/1.01  --res_time_limit                        2.
% 0.53/1.01  --res_out_proof                         true
% 0.53/1.01  
% 0.53/1.01  ------ Superposition Options
% 0.53/1.01  
% 0.53/1.01  --superposition_flag                    false
% 0.53/1.01  --sup_passive_queue_type                priority_queues
% 0.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.53/1.01  --demod_completeness_check              fast
% 0.53/1.01  --demod_use_ground                      true
% 0.53/1.01  --sup_to_prop_solver                    passive
% 0.53/1.01  --sup_prop_simpl_new                    true
% 0.53/1.01  --sup_prop_simpl_given                  true
% 0.53/1.01  --sup_fun_splitting                     false
% 0.53/1.01  --sup_smt_interval                      50000
% 0.53/1.01  
% 0.53/1.01  ------ Superposition Simplification Setup
% 0.53/1.01  
% 0.53/1.01  --sup_indices_passive                   []
% 0.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_full_bw                           [BwDemod]
% 0.53/1.01  --sup_immed_triv                        [TrivRules]
% 0.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_immed_bw_main                     []
% 0.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.53/1.01  
% 0.53/1.01  ------ Combination Options
% 0.53/1.01  
% 0.53/1.01  --comb_res_mult                         3
% 0.53/1.01  --comb_sup_mult                         2
% 0.53/1.01  --comb_inst_mult                        10
% 0.53/1.01  
% 0.53/1.01  ------ Debug Options
% 0.53/1.01  
% 0.53/1.01  --dbg_backtrace                         false
% 0.53/1.01  --dbg_dump_prop_clauses                 false
% 0.53/1.01  --dbg_dump_prop_clauses_file            -
% 0.53/1.01  --dbg_out_stat                          false
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  ------ Proving...
% 0.53/1.01  
% 0.53/1.01  
% 0.53/1.01  % SZS status Theorem for theBenchmark.p
% 0.53/1.01  
% 0.53/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.53/1.01  
% 0.53/1.01  fof(f3,axiom,(
% 0.53/1.01    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f15,plain,(
% 0.53/1.01    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.53/1.01    inference(ennf_transformation,[],[f3])).
% 0.53/1.01  
% 0.53/1.01  fof(f16,plain,(
% 0.53/1.01    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.53/1.01    inference(flattening,[],[f15])).
% 0.53/1.01  
% 0.53/1.01  fof(f36,plain,(
% 0.53/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f16])).
% 0.53/1.01  
% 0.53/1.01  fof(f5,axiom,(
% 0.53/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f18,plain,(
% 0.53/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.53/1.01    inference(ennf_transformation,[],[f5])).
% 0.53/1.01  
% 0.53/1.01  fof(f27,plain,(
% 0.53/1.01    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.53/1.01    inference(nnf_transformation,[],[f18])).
% 0.53/1.01  
% 0.53/1.01  fof(f28,plain,(
% 0.53/1.01    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.53/1.01    inference(rectify,[],[f27])).
% 0.53/1.01  
% 0.53/1.01  fof(f29,plain,(
% 0.53/1.01    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.53/1.01    introduced(choice_axiom,[])).
% 0.53/1.01  
% 0.53/1.01  fof(f30,plain,(
% 0.53/1.01    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 0.53/1.01  
% 0.53/1.01  fof(f39,plain,(
% 0.53/1.01    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f30])).
% 0.53/1.01  
% 0.53/1.01  fof(f40,plain,(
% 0.53/1.01    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK1(X0),X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f30])).
% 0.53/1.01  
% 0.53/1.01  fof(f8,axiom,(
% 0.53/1.01    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f21,plain,(
% 0.53/1.01    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.53/1.01    inference(ennf_transformation,[],[f8])).
% 0.53/1.01  
% 0.53/1.01  fof(f22,plain,(
% 0.53/1.01    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.53/1.01    inference(flattening,[],[f21])).
% 0.53/1.01  
% 0.53/1.01  fof(f43,plain,(
% 0.53/1.01    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f22])).
% 0.53/1.01  
% 0.53/1.01  fof(f7,axiom,(
% 0.53/1.01    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f19,plain,(
% 0.53/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.53/1.01    inference(ennf_transformation,[],[f7])).
% 0.53/1.01  
% 0.53/1.01  fof(f20,plain,(
% 0.53/1.01    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.53/1.01    inference(flattening,[],[f19])).
% 0.53/1.01  
% 0.53/1.01  fof(f42,plain,(
% 0.53/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f20])).
% 0.53/1.01  
% 0.53/1.01  fof(f38,plain,(
% 0.53/1.01    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f30])).
% 0.53/1.01  
% 0.53/1.01  fof(f2,axiom,(
% 0.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f14,plain,(
% 0.53/1.01    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.53/1.01    inference(ennf_transformation,[],[f2])).
% 0.53/1.01  
% 0.53/1.01  fof(f35,plain,(
% 0.53/1.01    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f14])).
% 0.53/1.01  
% 0.53/1.01  fof(f1,axiom,(
% 0.53/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f13,plain,(
% 0.53/1.01    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.53/1.01    inference(ennf_transformation,[],[f1])).
% 0.53/1.01  
% 0.53/1.01  fof(f25,plain,(
% 0.53/1.01    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.53/1.01    introduced(choice_axiom,[])).
% 0.53/1.01  
% 0.53/1.01  fof(f26,plain,(
% 0.53/1.01    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 0.53/1.01  
% 0.53/1.01  fof(f34,plain,(
% 0.53/1.01    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK0(X0,X1),X1)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f26])).
% 0.53/1.01  
% 0.53/1.01  fof(f33,plain,(
% 0.53/1.01    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f26])).
% 0.53/1.01  
% 0.53/1.01  fof(f4,axiom,(
% 0.53/1.01    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f12,plain,(
% 0.53/1.01    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.53/1.01    inference(pure_predicate_removal,[],[f4])).
% 0.53/1.01  
% 0.53/1.01  fof(f17,plain,(
% 0.53/1.01    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.53/1.01    inference(ennf_transformation,[],[f12])).
% 0.53/1.01  
% 0.53/1.01  fof(f37,plain,(
% 0.53/1.01    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f17])).
% 0.53/1.01  
% 0.53/1.01  fof(f6,axiom,(
% 0.53/1.01    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f41,plain,(
% 0.53/1.01    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.53/1.01    inference(cnf_transformation,[],[f6])).
% 0.53/1.01  
% 0.53/1.01  fof(f9,axiom,(
% 0.53/1.01    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f23,plain,(
% 0.53/1.01    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.53/1.01    inference(ennf_transformation,[],[f9])).
% 0.53/1.01  
% 0.53/1.01  fof(f44,plain,(
% 0.53/1.01    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.53/1.01    inference(cnf_transformation,[],[f23])).
% 0.53/1.01  
% 0.53/1.01  fof(f10,conjecture,(
% 0.53/1.01    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.53/1.01  
% 0.53/1.01  fof(f11,negated_conjecture,(
% 0.53/1.01    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.53/1.01    inference(negated_conjecture,[],[f10])).
% 0.53/1.01  
% 0.53/1.01  fof(f24,plain,(
% 0.53/1.01    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.53/1.01    inference(ennf_transformation,[],[f11])).
% 0.53/1.01  
% 0.53/1.01  fof(f31,plain,(
% 0.53/1.01    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK2)) & v3_ordinal1(sK2))),
% 0.53/1.01    introduced(choice_axiom,[])).
% 0.53/1.01  
% 0.53/1.01  fof(f32,plain,(
% 0.53/1.01    ~v3_ordinal1(k3_tarski(sK2)) & v3_ordinal1(sK2)),
% 0.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f31])).
% 0.53/1.01  
% 0.53/1.01  fof(f46,plain,(
% 0.53/1.01    ~v3_ordinal1(k3_tarski(sK2))),
% 0.53/1.01    inference(cnf_transformation,[],[f32])).
% 0.53/1.01  
% 0.53/1.01  fof(f45,plain,(
% 0.53/1.01    v3_ordinal1(sK2)),
% 0.53/1.01    inference(cnf_transformation,[],[f32])).
% 0.53/1.01  
% 0.53/1.01  cnf(c_3,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,X1)
% 0.53/1.01      | r1_tarski(X0,X2)
% 0.53/1.01      | ~ r1_tarski(k3_tarski(X1),X2) ),
% 0.53/1.01      inference(cnf_transformation,[],[f36]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_529,plain,
% 0.53/1.01      ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | r1_tarski(sK1(k3_tarski(sK2)),X0)
% 0.53/1.01      | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),X0) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_636,plain,
% 0.53/1.01      ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(X0))
% 0.53/1.01      | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(X0)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_529]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_639,plain,
% 0.53/1.01      ( ~ r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | ~ r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_636]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_6,plain,
% 0.53/1.01      ( r2_hidden(sK1(X0),X0) | v1_ordinal1(X0) ),
% 0.53/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_438,plain,
% 0.53/1.01      ( r2_hidden(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | v1_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_5,plain,
% 0.53/1.01      ( ~ r1_tarski(sK1(X0),X0) | v1_ordinal1(X0) ),
% 0.53/1.01      inference(cnf_transformation,[],[f40]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_439,plain,
% 0.53/1.01      ( ~ r1_tarski(sK1(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | v1_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_10,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 0.53/1.01      inference(cnf_transformation,[],[f43]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_333,plain,
% 0.53/1.01      ( ~ r2_hidden(k3_tarski(sK2),X0)
% 0.53/1.01      | ~ v3_ordinal1(X0)
% 0.53/1.01      | v3_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_388,plain,
% 0.53/1.01      ( ~ r2_hidden(k3_tarski(sK2),k1_ordinal1(X0))
% 0.53/1.01      | ~ v3_ordinal1(k1_ordinal1(X0))
% 0.53/1.01      | v3_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_333]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_394,plain,
% 0.53/1.01      ( ~ r2_hidden(k3_tarski(sK2),k1_ordinal1(sK2))
% 0.53/1.01      | ~ v3_ordinal1(k1_ordinal1(sK2))
% 0.53/1.01      | v3_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_388]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_9,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,X1)
% 0.53/1.01      | r2_hidden(X2,X1)
% 0.53/1.01      | ~ r1_tarski(X2,X0)
% 0.53/1.01      | ~ v3_ordinal1(X1)
% 0.53/1.01      | ~ v3_ordinal1(X0)
% 0.53/1.01      | ~ v1_ordinal1(X2) ),
% 0.53/1.01      inference(cnf_transformation,[],[f42]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_81,plain,
% 0.53/1.01      ( ~ v3_ordinal1(X1)
% 0.53/1.01      | ~ r1_tarski(X2,X0)
% 0.53/1.01      | r2_hidden(X2,X1)
% 0.53/1.01      | ~ r2_hidden(X0,X1)
% 0.53/1.01      | ~ v1_ordinal1(X2) ),
% 0.53/1.01      inference(global_propositional_subsumption,
% 0.53/1.01                [status(thm)],
% 0.53/1.01                [c_9,c_10]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_82,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,X1)
% 0.53/1.01      | r2_hidden(X2,X1)
% 0.53/1.01      | ~ r1_tarski(X2,X0)
% 0.53/1.01      | ~ v3_ordinal1(X1)
% 0.53/1.01      | ~ v1_ordinal1(X2) ),
% 0.53/1.01      inference(renaming,[status(thm)],[c_81]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_344,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 0.53/1.01      | r2_hidden(X1,k1_ordinal1(X0))
% 0.53/1.01      | ~ r1_tarski(X1,X0)
% 0.53/1.01      | ~ v3_ordinal1(k1_ordinal1(X0))
% 0.53/1.01      | ~ v1_ordinal1(X1) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_82]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_387,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 0.53/1.01      | r2_hidden(k3_tarski(sK2),k1_ordinal1(X0))
% 0.53/1.01      | ~ r1_tarski(k3_tarski(sK2),X0)
% 0.53/1.01      | ~ v3_ordinal1(k1_ordinal1(X0))
% 0.53/1.01      | ~ v1_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_344]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_390,plain,
% 0.53/1.01      ( r2_hidden(k3_tarski(sK2),k1_ordinal1(sK2))
% 0.53/1.01      | ~ r2_hidden(sK2,k1_ordinal1(sK2))
% 0.53/1.01      | ~ r1_tarski(k3_tarski(sK2),sK2)
% 0.53/1.01      | ~ v3_ordinal1(k1_ordinal1(sK2))
% 0.53/1.01      | ~ v1_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_387]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_7,plain,
% 0.53/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 0.53/1.01      inference(cnf_transformation,[],[f38]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_363,plain,
% 0.53/1.01      ( ~ r2_hidden(sK0(X0,X1),X0)
% 0.53/1.01      | r1_tarski(sK0(X0,X1),X0)
% 0.53/1.01      | ~ v1_ordinal1(X0) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_375,plain,
% 0.53/1.01      ( ~ r2_hidden(sK0(sK2,sK2),sK2)
% 0.53/1.01      | r1_tarski(sK0(sK2,sK2),sK2)
% 0.53/1.01      | ~ v1_ordinal1(sK2) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_363]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_2,plain,
% 0.53/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 0.53/1.01      inference(cnf_transformation,[],[f35]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_338,plain,
% 0.53/1.01      ( ~ r1_tarski(k3_tarski(X0),X1)
% 0.53/1.01      | r1_tarski(k3_tarski(k3_tarski(X0)),k3_tarski(X1)) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 0.53/1.01  
% 0.53/1.01  cnf(c_340,plain,
% 0.53/1.01      ( r1_tarski(k3_tarski(k3_tarski(sK2)),k3_tarski(sK2))
% 0.53/1.01      | ~ r1_tarski(k3_tarski(sK2),sK2) ),
% 0.53/1.01      inference(instantiation,[status(thm)],[c_338]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_0,plain,
% 0.53/1.02      ( ~ r1_tarski(sK0(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 0.53/1.02      inference(cnf_transformation,[],[f34]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_46,plain,
% 0.53/1.02      ( ~ r1_tarski(sK0(sK2,sK2),sK2) | r1_tarski(k3_tarski(sK2),sK2) ),
% 0.53/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_1,plain,
% 0.53/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 0.53/1.02      inference(cnf_transformation,[],[f33]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_43,plain,
% 0.53/1.02      ( r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(k3_tarski(sK2),sK2) ),
% 0.53/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_4,plain,
% 0.53/1.02      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 0.53/1.02      inference(cnf_transformation,[],[f37]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_34,plain,
% 0.53/1.02      ( ~ v3_ordinal1(sK2) | v1_ordinal1(sK2) ),
% 0.53/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_8,plain,
% 0.53/1.02      ( r2_hidden(X0,k1_ordinal1(X0)) ),
% 0.53/1.02      inference(cnf_transformation,[],[f41]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_22,plain,
% 0.53/1.02      ( r2_hidden(sK2,k1_ordinal1(sK2)) ),
% 0.53/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_11,plain,
% 0.53/1.02      ( ~ v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0)) ),
% 0.53/1.02      inference(cnf_transformation,[],[f44]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_17,plain,
% 0.53/1.02      ( v3_ordinal1(k1_ordinal1(sK2)) | ~ v3_ordinal1(sK2) ),
% 0.53/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_12,negated_conjecture,
% 0.53/1.02      ( ~ v3_ordinal1(k3_tarski(sK2)) ),
% 0.53/1.02      inference(cnf_transformation,[],[f46]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(c_13,negated_conjecture,
% 0.53/1.02      ( v3_ordinal1(sK2) ),
% 0.53/1.02      inference(cnf_transformation,[],[f45]) ).
% 0.53/1.02  
% 0.53/1.02  cnf(contradiction,plain,
% 0.53/1.02      ( $false ),
% 0.53/1.02      inference(minisat,
% 0.53/1.02                [status(thm)],
% 0.53/1.02                [c_639,c_438,c_439,c_394,c_390,c_375,c_340,c_46,c_43,
% 0.53/1.02                 c_34,c_22,c_17,c_12,c_13]) ).
% 0.53/1.02  
% 0.53/1.02  
% 0.53/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.53/1.02  
% 0.53/1.02  ------                               Statistics
% 0.53/1.02  
% 0.53/1.02  ------ General
% 0.53/1.02  
% 0.53/1.02  abstr_ref_over_cycles:                  0
% 0.53/1.02  abstr_ref_under_cycles:                 0
% 0.53/1.02  gc_basic_clause_elim:                   0
% 0.53/1.02  forced_gc_time:                         0
% 0.53/1.02  parsing_time:                           0.012
% 0.53/1.02  unif_index_cands_time:                  0.
% 0.53/1.02  unif_index_add_time:                    0.
% 0.53/1.02  orderings_time:                         0.
% 0.53/1.02  out_proof_time:                         0.011
% 0.53/1.02  total_time:                             0.056
% 0.53/1.02  num_of_symbols:                         40
% 0.53/1.02  num_of_terms:                           742
% 0.53/1.02  
% 0.53/1.02  ------ Preprocessing
% 0.53/1.02  
% 0.53/1.02  num_of_splits:                          0
% 0.53/1.02  num_of_split_atoms:                     0
% 0.53/1.02  num_of_reused_defs:                     0
% 0.53/1.02  num_eq_ax_congr_red:                    0
% 0.53/1.02  num_of_sem_filtered_clauses:            0
% 0.53/1.02  num_of_subtypes:                        1
% 0.53/1.02  monotx_restored_types:                  0
% 0.53/1.02  sat_num_of_epr_types:                   0
% 0.53/1.02  sat_num_of_non_cyclic_types:            0
% 0.53/1.02  sat_guarded_non_collapsed_types:        0
% 0.53/1.02  num_pure_diseq_elim:                    0
% 0.53/1.02  simp_replaced_by:                       0
% 0.53/1.02  res_preprocessed:                       14
% 0.53/1.02  prep_upred:                             0
% 0.53/1.02  prep_unflattend:                        0
% 0.53/1.02  smt_new_axioms:                         0
% 0.53/1.02  pred_elim_cands:                        4
% 0.53/1.02  pred_elim:                              0
% 0.53/1.02  pred_elim_cl:                           0
% 0.53/1.02  pred_elim_cycles:                       1
% 0.53/1.02  merged_defs:                            0
% 0.53/1.02  merged_defs_ncl:                        0
% 0.53/1.02  bin_hyper_res:                          0
% 0.53/1.02  prep_cycles:                            1
% 0.53/1.02  pred_elim_time:                         0.001
% 0.53/1.02  splitting_time:                         0.
% 0.53/1.02  sem_filter_time:                        0.
% 0.53/1.02  monotx_time:                            0.
% 0.53/1.02  subtype_inf_time:                       0.
% 0.53/1.02  
% 0.53/1.02  ------ Problem properties
% 0.53/1.02  
% 0.53/1.02  clauses:                                14
% 0.53/1.02  conjectures:                            2
% 0.53/1.02  epr:                                    5
% 0.53/1.02  horn:                                   12
% 0.53/1.02  ground:                                 2
% 0.53/1.02  unary:                                  3
% 0.53/1.02  binary:                                 7
% 0.53/1.02  lits:                                   31
% 0.53/1.02  lits_eq:                                0
% 0.53/1.02  fd_pure:                                0
% 0.53/1.02  fd_pseudo:                              0
% 0.53/1.02  fd_cond:                                0
% 0.53/1.02  fd_pseudo_cond:                         0
% 0.53/1.02  ac_symbols:                             0
% 0.53/1.02  
% 0.53/1.02  ------ Propositional Solver
% 0.53/1.02  
% 0.53/1.02  prop_solver_calls:                      12
% 0.53/1.02  prop_fast_solver_calls:                 92
% 0.53/1.02  smt_solver_calls:                       0
% 0.53/1.02  smt_fast_solver_calls:                  0
% 0.53/1.02  prop_num_of_clauses:                    253
% 0.53/1.02  prop_preprocess_simplified:             966
% 0.53/1.02  prop_fo_subsumed:                       1
% 0.53/1.02  prop_solver_time:                       0.
% 0.53/1.02  smt_solver_time:                        0.
% 0.53/1.02  smt_fast_solver_time:                   0.
% 0.53/1.02  prop_fast_solver_time:                  0.
% 0.53/1.02  prop_unsat_core_time:                   0.
% 0.53/1.02  
% 0.53/1.02  ------ QBF
% 0.53/1.02  
% 0.53/1.02  qbf_q_res:                              0
% 0.53/1.02  qbf_num_tautologies:                    0
% 0.53/1.02  qbf_prep_cycles:                        0
% 0.53/1.02  
% 0.53/1.02  ------ BMC1
% 0.53/1.02  
% 0.53/1.02  bmc1_current_bound:                     -1
% 0.53/1.02  bmc1_last_solved_bound:                 -1
% 0.53/1.02  bmc1_unsat_core_size:                   -1
% 0.53/1.02  bmc1_unsat_core_parents_size:           -1
% 0.53/1.02  bmc1_merge_next_fun:                    0
% 0.53/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.53/1.02  
% 0.53/1.02  ------ Instantiation
% 0.53/1.02  
% 0.53/1.02  inst_num_of_clauses:                    69
% 0.53/1.02  inst_num_in_passive:                    23
% 0.53/1.02  inst_num_in_active:                     42
% 0.53/1.02  inst_num_in_unprocessed:                3
% 0.53/1.02  inst_num_of_loops:                      50
% 0.53/1.02  inst_num_of_learning_restarts:          0
% 0.53/1.02  inst_num_moves_active_passive:          5
% 0.53/1.02  inst_lit_activity:                      0
% 0.53/1.02  inst_lit_activity_moves:                0
% 0.53/1.02  inst_num_tautologies:                   0
% 0.53/1.02  inst_num_prop_implied:                  0
% 0.53/1.02  inst_num_existing_simplified:           0
% 0.53/1.02  inst_num_eq_res_simplified:             0
% 0.53/1.02  inst_num_child_elim:                    0
% 0.53/1.02  inst_num_of_dismatching_blockings:      9
% 0.53/1.02  inst_num_of_non_proper_insts:           35
% 0.53/1.02  inst_num_of_duplicates:                 0
% 0.53/1.02  inst_inst_num_from_inst_to_res:         0
% 0.53/1.02  inst_dismatching_checking_time:         0.
% 0.53/1.02  
% 0.53/1.02  ------ Resolution
% 0.53/1.02  
% 0.53/1.02  res_num_of_clauses:                     0
% 0.53/1.02  res_num_in_passive:                     0
% 0.53/1.02  res_num_in_active:                      0
% 0.53/1.02  res_num_of_loops:                       15
% 0.53/1.02  res_forward_subset_subsumed:            5
% 0.53/1.02  res_backward_subset_subsumed:           0
% 0.53/1.02  res_forward_subsumed:                   0
% 0.53/1.02  res_backward_subsumed:                  0
% 0.53/1.02  res_forward_subsumption_resolution:     0
% 0.53/1.02  res_backward_subsumption_resolution:    0
% 0.53/1.02  res_clause_to_clause_subsumption:       10
% 0.53/1.02  res_orphan_elimination:                 0
% 0.53/1.02  res_tautology_del:                      0
% 0.53/1.02  res_num_eq_res_simplified:              0
% 0.53/1.02  res_num_sel_changes:                    0
% 0.53/1.02  res_moves_from_active_to_pass:          0
% 0.53/1.02  
% 0.53/1.02  ------ Superposition
% 0.53/1.02  
% 0.53/1.02  sup_time_total:                         0.
% 0.53/1.02  sup_time_generating:                    0.
% 0.53/1.02  sup_time_sim_full:                      0.
% 0.53/1.02  sup_time_sim_immed:                     0.
% 0.53/1.02  
% 0.53/1.02  sup_num_of_clauses:                     0
% 0.53/1.02  sup_num_in_active:                      0
% 0.53/1.02  sup_num_in_passive:                     0
% 0.53/1.02  sup_num_of_loops:                       0
% 0.53/1.02  sup_fw_superposition:                   0
% 0.53/1.02  sup_bw_superposition:                   0
% 0.53/1.02  sup_immediate_simplified:               0
% 0.53/1.02  sup_given_eliminated:                   0
% 0.53/1.02  comparisons_done:                       0
% 0.53/1.02  comparisons_avoided:                    0
% 0.53/1.02  
% 0.53/1.02  ------ Simplifications
% 0.53/1.02  
% 0.53/1.02  
% 0.53/1.02  sim_fw_subset_subsumed:                 0
% 0.53/1.02  sim_bw_subset_subsumed:                 0
% 0.53/1.02  sim_fw_subsumed:                        0
% 0.53/1.02  sim_bw_subsumed:                        0
% 0.53/1.02  sim_fw_subsumption_res:                 0
% 0.53/1.02  sim_bw_subsumption_res:                 0
% 0.53/1.02  sim_tautology_del:                      0
% 0.53/1.02  sim_eq_tautology_del:                   0
% 0.53/1.02  sim_eq_res_simp:                        0
% 0.53/1.02  sim_fw_demodulated:                     0
% 0.53/1.02  sim_bw_demodulated:                     0
% 0.53/1.02  sim_light_normalised:                   0
% 0.53/1.02  sim_joinable_taut:                      0
% 0.53/1.02  sim_joinable_simp:                      0
% 0.53/1.02  sim_ac_normalised:                      0
% 0.53/1.02  sim_smt_subsumption:                    0
% 0.53/1.02  
%------------------------------------------------------------------------------
