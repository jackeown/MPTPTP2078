%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:33 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of clauses        :   35 (  40 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 556 expanded)
%              Number of equality atoms :   29 (  53 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
     => v2_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f24])).

fof(f35,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK3)
      & ! [X1] :
          ( ( r1_tarski(X1,sK3)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v3_ordinal1(sK3)
    & ! [X1] :
        ( ( r1_tarski(X1,sK3)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).

fof(f43,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).

fof(f33,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK3)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ~ v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1356,plain,
    ( ~ r1_tarski(sK1(X0),sK2(X0))
    | ~ r1_tarski(sK2(X0),sK1(X0))
    | sK1(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1358,plain,
    ( ~ r1_tarski(sK1(sK3),sK2(sK3))
    | ~ r1_tarski(sK2(sK3),sK1(sK3))
    | sK1(sK3) = sK2(sK3) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_497,plain,
    ( v2_ordinal1(X0)
    | v3_ordinal1(X1)
    | sK1(X0) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_498,plain,
    ( v2_ordinal1(sK3)
    | v3_ordinal1(sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_475,plain,
    ( v2_ordinal1(X0)
    | v3_ordinal1(X1)
    | sK2(X0) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_476,plain,
    ( v2_ordinal1(sK3)
    | v3_ordinal1(sK2(sK3)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_222,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_12])).

cnf(c_457,plain,
    ( r1_tarski(X0,X1)
    | v2_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK1(X2) != X1
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_222])).

cnf(c_458,plain,
    ( r1_tarski(sK2(X0),sK1(X0))
    | v2_ordinal1(X0)
    | ~ v3_ordinal1(sK1(X0))
    | ~ v3_ordinal1(sK2(X0)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( r1_tarski(sK2(sK3),sK1(sK3))
    | v2_ordinal1(sK3)
    | ~ v3_ordinal1(sK1(sK3))
    | ~ v3_ordinal1(sK2(sK3)) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_409,plain,
    ( r1_tarski(X0,X1)
    | v2_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK1(X2) != X0
    | sK2(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_222])).

cnf(c_410,plain,
    ( r1_tarski(sK1(X0),sK2(X0))
    | v2_ordinal1(X0)
    | ~ v3_ordinal1(sK1(X0))
    | ~ v3_ordinal1(sK2(X0)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( r1_tarski(sK1(sK3),sK2(sK3))
    | v2_ordinal1(sK3)
    | ~ v3_ordinal1(sK1(sK3))
    | ~ v3_ordinal1(sK2(sK3)) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_368,plain,
    ( r1_tarski(X0,sK3)
    | v1_ordinal1(X1)
    | sK0(X1) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_369,plain,
    ( r1_tarski(sK0(sK3),sK3)
    | v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_4,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_46,plain,
    ( ~ r1_tarski(sK0(sK3),sK3)
    | v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_371,plain,
    ( v1_ordinal1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_46])).

cnf(c_7,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ v1_ordinal1(X0)
    | ~ v2_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_285,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_287,plain,
    ( ~ v1_ordinal1(sK3)
    | v3_ordinal1(sK3)
    | sK1(sK3) != sK2(sK3) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_49,plain,
    ( ~ v1_ordinal1(sK3)
    | ~ v2_ordinal1(sK3)
    | v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( ~ v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1358,c_498,c_476,c_460,c_412,c_371,c_287,c_49,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.81/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.81/1.01  
% 0.81/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.81/1.01  
% 0.81/1.01  ------  iProver source info
% 0.81/1.01  
% 0.81/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.81/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.81/1.01  git: non_committed_changes: false
% 0.81/1.01  git: last_make_outside_of_git: false
% 0.81/1.01  
% 0.81/1.01  ------ 
% 0.81/1.01  
% 0.81/1.01  ------ Input Options
% 0.81/1.01  
% 0.81/1.01  --out_options                           all
% 0.81/1.01  --tptp_safe_out                         true
% 0.81/1.01  --problem_path                          ""
% 0.81/1.01  --include_path                          ""
% 0.81/1.01  --clausifier                            res/vclausify_rel
% 0.81/1.01  --clausifier_options                    --mode clausify
% 0.81/1.01  --stdin                                 false
% 0.81/1.01  --stats_out                             all
% 0.81/1.01  
% 0.81/1.01  ------ General Options
% 0.81/1.01  
% 0.81/1.01  --fof                                   false
% 0.81/1.01  --time_out_real                         305.
% 0.81/1.01  --time_out_virtual                      -1.
% 0.81/1.01  --symbol_type_check                     false
% 0.81/1.01  --clausify_out                          false
% 0.81/1.01  --sig_cnt_out                           false
% 0.81/1.01  --trig_cnt_out                          false
% 0.81/1.01  --trig_cnt_out_tolerance                1.
% 0.81/1.01  --trig_cnt_out_sk_spl                   false
% 0.81/1.01  --abstr_cl_out                          false
% 0.81/1.01  
% 0.81/1.01  ------ Global Options
% 0.81/1.01  
% 0.81/1.01  --schedule                              default
% 0.81/1.01  --add_important_lit                     false
% 0.81/1.01  --prop_solver_per_cl                    1000
% 0.81/1.01  --min_unsat_core                        false
% 0.81/1.01  --soft_assumptions                      false
% 0.81/1.01  --soft_lemma_size                       3
% 0.81/1.01  --prop_impl_unit_size                   0
% 0.81/1.01  --prop_impl_unit                        []
% 0.81/1.01  --share_sel_clauses                     true
% 0.81/1.01  --reset_solvers                         false
% 0.81/1.01  --bc_imp_inh                            [conj_cone]
% 0.81/1.01  --conj_cone_tolerance                   3.
% 0.81/1.01  --extra_neg_conj                        none
% 0.81/1.01  --large_theory_mode                     true
% 0.81/1.01  --prolific_symb_bound                   200
% 0.81/1.01  --lt_threshold                          2000
% 0.81/1.01  --clause_weak_htbl                      true
% 0.81/1.01  --gc_record_bc_elim                     false
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing Options
% 0.81/1.01  
% 0.81/1.01  --preprocessing_flag                    true
% 0.81/1.01  --time_out_prep_mult                    0.1
% 0.81/1.01  --splitting_mode                        input
% 0.81/1.01  --splitting_grd                         true
% 0.81/1.01  --splitting_cvd                         false
% 0.81/1.01  --splitting_cvd_svl                     false
% 0.81/1.01  --splitting_nvd                         32
% 0.81/1.01  --sub_typing                            true
% 0.81/1.01  --prep_gs_sim                           true
% 0.81/1.01  --prep_unflatten                        true
% 0.81/1.01  --prep_res_sim                          true
% 0.81/1.01  --prep_upred                            true
% 0.81/1.01  --prep_sem_filter                       exhaustive
% 0.81/1.01  --prep_sem_filter_out                   false
% 0.81/1.01  --pred_elim                             true
% 0.81/1.01  --res_sim_input                         true
% 0.81/1.01  --eq_ax_congr_red                       true
% 0.81/1.01  --pure_diseq_elim                       true
% 0.81/1.01  --brand_transform                       false
% 0.81/1.01  --non_eq_to_eq                          false
% 0.81/1.01  --prep_def_merge                        true
% 0.81/1.01  --prep_def_merge_prop_impl              false
% 0.81/1.01  --prep_def_merge_mbd                    true
% 0.81/1.01  --prep_def_merge_tr_red                 false
% 0.81/1.01  --prep_def_merge_tr_cl                  false
% 0.81/1.01  --smt_preprocessing                     true
% 0.81/1.01  --smt_ac_axioms                         fast
% 0.81/1.01  --preprocessed_out                      false
% 0.81/1.01  --preprocessed_stats                    false
% 0.81/1.01  
% 0.81/1.01  ------ Abstraction refinement Options
% 0.81/1.01  
% 0.81/1.01  --abstr_ref                             []
% 0.81/1.01  --abstr_ref_prep                        false
% 0.81/1.01  --abstr_ref_until_sat                   false
% 0.81/1.01  --abstr_ref_sig_restrict                funpre
% 0.81/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/1.01  --abstr_ref_under                       []
% 0.81/1.01  
% 0.81/1.01  ------ SAT Options
% 0.81/1.01  
% 0.81/1.01  --sat_mode                              false
% 0.81/1.01  --sat_fm_restart_options                ""
% 0.81/1.01  --sat_gr_def                            false
% 0.81/1.01  --sat_epr_types                         true
% 0.81/1.01  --sat_non_cyclic_types                  false
% 0.81/1.01  --sat_finite_models                     false
% 0.81/1.01  --sat_fm_lemmas                         false
% 0.81/1.01  --sat_fm_prep                           false
% 0.81/1.01  --sat_fm_uc_incr                        true
% 0.81/1.01  --sat_out_model                         small
% 0.81/1.01  --sat_out_clauses                       false
% 0.81/1.01  
% 0.81/1.01  ------ QBF Options
% 0.81/1.01  
% 0.81/1.01  --qbf_mode                              false
% 0.81/1.01  --qbf_elim_univ                         false
% 0.81/1.01  --qbf_dom_inst                          none
% 0.81/1.01  --qbf_dom_pre_inst                      false
% 0.81/1.01  --qbf_sk_in                             false
% 0.81/1.01  --qbf_pred_elim                         true
% 0.81/1.01  --qbf_split                             512
% 0.81/1.01  
% 0.81/1.01  ------ BMC1 Options
% 0.81/1.01  
% 0.81/1.01  --bmc1_incremental                      false
% 0.81/1.01  --bmc1_axioms                           reachable_all
% 0.81/1.01  --bmc1_min_bound                        0
% 0.81/1.01  --bmc1_max_bound                        -1
% 0.81/1.01  --bmc1_max_bound_default                -1
% 0.81/1.01  --bmc1_symbol_reachability              true
% 0.81/1.01  --bmc1_property_lemmas                  false
% 0.81/1.01  --bmc1_k_induction                      false
% 0.81/1.01  --bmc1_non_equiv_states                 false
% 0.81/1.01  --bmc1_deadlock                         false
% 0.81/1.01  --bmc1_ucm                              false
% 0.81/1.01  --bmc1_add_unsat_core                   none
% 0.81/1.01  --bmc1_unsat_core_children              false
% 0.81/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/1.01  --bmc1_out_stat                         full
% 0.81/1.01  --bmc1_ground_init                      false
% 0.81/1.01  --bmc1_pre_inst_next_state              false
% 0.81/1.01  --bmc1_pre_inst_state                   false
% 0.81/1.01  --bmc1_pre_inst_reach_state             false
% 0.81/1.01  --bmc1_out_unsat_core                   false
% 0.81/1.01  --bmc1_aig_witness_out                  false
% 0.81/1.01  --bmc1_verbose                          false
% 0.81/1.01  --bmc1_dump_clauses_tptp                false
% 0.81/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.81/1.01  --bmc1_dump_file                        -
% 0.81/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.81/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.81/1.01  --bmc1_ucm_extend_mode                  1
% 0.81/1.01  --bmc1_ucm_init_mode                    2
% 0.81/1.01  --bmc1_ucm_cone_mode                    none
% 0.81/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.81/1.01  --bmc1_ucm_relax_model                  4
% 0.81/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.81/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/1.01  --bmc1_ucm_layered_model                none
% 0.81/1.01  --bmc1_ucm_max_lemma_size               10
% 0.81/1.01  
% 0.81/1.01  ------ AIG Options
% 0.81/1.01  
% 0.81/1.01  --aig_mode                              false
% 0.81/1.01  
% 0.81/1.01  ------ Instantiation Options
% 0.81/1.01  
% 0.81/1.01  --instantiation_flag                    true
% 0.81/1.01  --inst_sos_flag                         false
% 0.81/1.01  --inst_sos_phase                        true
% 0.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/1.01  --inst_lit_sel_side                     num_symb
% 0.81/1.01  --inst_solver_per_active                1400
% 0.81/1.01  --inst_solver_calls_frac                1.
% 0.81/1.01  --inst_passive_queue_type               priority_queues
% 0.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/1.01  --inst_passive_queues_freq              [25;2]
% 0.81/1.01  --inst_dismatching                      true
% 0.81/1.01  --inst_eager_unprocessed_to_passive     true
% 0.81/1.01  --inst_prop_sim_given                   true
% 0.81/1.01  --inst_prop_sim_new                     false
% 0.81/1.01  --inst_subs_new                         false
% 0.81/1.01  --inst_eq_res_simp                      false
% 0.81/1.01  --inst_subs_given                       false
% 0.81/1.01  --inst_orphan_elimination               true
% 0.81/1.01  --inst_learning_loop_flag               true
% 0.81/1.01  --inst_learning_start                   3000
% 0.81/1.01  --inst_learning_factor                  2
% 0.81/1.01  --inst_start_prop_sim_after_learn       3
% 0.81/1.01  --inst_sel_renew                        solver
% 0.81/1.01  --inst_lit_activity_flag                true
% 0.81/1.01  --inst_restr_to_given                   false
% 0.81/1.01  --inst_activity_threshold               500
% 0.81/1.01  --inst_out_proof                        true
% 0.81/1.01  
% 0.81/1.01  ------ Resolution Options
% 0.81/1.01  
% 0.81/1.01  --resolution_flag                       true
% 0.81/1.01  --res_lit_sel                           adaptive
% 0.81/1.01  --res_lit_sel_side                      none
% 0.81/1.01  --res_ordering                          kbo
% 0.81/1.01  --res_to_prop_solver                    active
% 0.81/1.01  --res_prop_simpl_new                    false
% 0.81/1.01  --res_prop_simpl_given                  true
% 0.81/1.01  --res_passive_queue_type                priority_queues
% 0.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/1.01  --res_passive_queues_freq               [15;5]
% 0.81/1.01  --res_forward_subs                      full
% 0.81/1.01  --res_backward_subs                     full
% 0.81/1.01  --res_forward_subs_resolution           true
% 0.81/1.01  --res_backward_subs_resolution          true
% 0.81/1.01  --res_orphan_elimination                true
% 0.81/1.01  --res_time_limit                        2.
% 0.81/1.01  --res_out_proof                         true
% 0.81/1.01  
% 0.81/1.01  ------ Superposition Options
% 0.81/1.01  
% 0.81/1.01  --superposition_flag                    true
% 0.81/1.01  --sup_passive_queue_type                priority_queues
% 0.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.81/1.01  --demod_completeness_check              fast
% 0.81/1.01  --demod_use_ground                      true
% 0.81/1.01  --sup_to_prop_solver                    passive
% 0.81/1.01  --sup_prop_simpl_new                    true
% 0.81/1.01  --sup_prop_simpl_given                  true
% 0.81/1.01  --sup_fun_splitting                     false
% 0.81/1.01  --sup_smt_interval                      50000
% 0.81/1.01  
% 0.81/1.01  ------ Superposition Simplification Setup
% 0.81/1.01  
% 0.81/1.01  --sup_indices_passive                   []
% 0.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_full_bw                           [BwDemod]
% 0.81/1.01  --sup_immed_triv                        [TrivRules]
% 0.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_immed_bw_main                     []
% 0.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/1.01  
% 0.81/1.01  ------ Combination Options
% 0.81/1.01  
% 0.81/1.01  --comb_res_mult                         3
% 0.81/1.01  --comb_sup_mult                         2
% 0.81/1.01  --comb_inst_mult                        10
% 0.81/1.01  
% 0.81/1.01  ------ Debug Options
% 0.81/1.01  
% 0.81/1.01  --dbg_backtrace                         false
% 0.81/1.01  --dbg_dump_prop_clauses                 false
% 0.81/1.01  --dbg_dump_prop_clauses_file            -
% 0.81/1.01  --dbg_out_stat                          false
% 0.81/1.01  ------ Parsing...
% 0.81/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.81/1.01  ------ Proving...
% 0.81/1.01  ------ Problem Properties 
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  clauses                                 14
% 0.81/1.01  conjectures                             3
% 0.81/1.01  EPR                                     7
% 0.81/1.01  Horn                                    10
% 0.81/1.01  unary                                   2
% 0.81/1.01  binary                                  9
% 0.81/1.01  lits                                    30
% 0.81/1.01  lits eq                                 2
% 0.81/1.01  fd_pure                                 0
% 0.81/1.01  fd_pseudo                               0
% 0.81/1.01  fd_cond                                 0
% 0.81/1.01  fd_pseudo_cond                          1
% 0.81/1.01  AC symbols                              0
% 0.81/1.01  
% 0.81/1.01  ------ Schedule dynamic 5 is on 
% 0.81/1.01  
% 0.81/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  ------ 
% 0.81/1.01  Current options:
% 0.81/1.01  ------ 
% 0.81/1.01  
% 0.81/1.01  ------ Input Options
% 0.81/1.01  
% 0.81/1.01  --out_options                           all
% 0.81/1.01  --tptp_safe_out                         true
% 0.81/1.01  --problem_path                          ""
% 0.81/1.01  --include_path                          ""
% 0.81/1.01  --clausifier                            res/vclausify_rel
% 0.81/1.01  --clausifier_options                    --mode clausify
% 0.81/1.01  --stdin                                 false
% 0.81/1.01  --stats_out                             all
% 0.81/1.01  
% 0.81/1.01  ------ General Options
% 0.81/1.01  
% 0.81/1.01  --fof                                   false
% 0.81/1.01  --time_out_real                         305.
% 0.81/1.01  --time_out_virtual                      -1.
% 0.81/1.01  --symbol_type_check                     false
% 0.81/1.01  --clausify_out                          false
% 0.81/1.01  --sig_cnt_out                           false
% 0.81/1.01  --trig_cnt_out                          false
% 0.81/1.01  --trig_cnt_out_tolerance                1.
% 0.81/1.01  --trig_cnt_out_sk_spl                   false
% 0.81/1.01  --abstr_cl_out                          false
% 0.81/1.01  
% 0.81/1.01  ------ Global Options
% 0.81/1.01  
% 0.81/1.01  --schedule                              default
% 0.81/1.01  --add_important_lit                     false
% 0.81/1.01  --prop_solver_per_cl                    1000
% 0.81/1.01  --min_unsat_core                        false
% 0.81/1.01  --soft_assumptions                      false
% 0.81/1.01  --soft_lemma_size                       3
% 0.81/1.01  --prop_impl_unit_size                   0
% 0.81/1.01  --prop_impl_unit                        []
% 0.81/1.01  --share_sel_clauses                     true
% 0.81/1.01  --reset_solvers                         false
% 0.81/1.01  --bc_imp_inh                            [conj_cone]
% 0.81/1.01  --conj_cone_tolerance                   3.
% 0.81/1.01  --extra_neg_conj                        none
% 0.81/1.01  --large_theory_mode                     true
% 0.81/1.01  --prolific_symb_bound                   200
% 0.81/1.01  --lt_threshold                          2000
% 0.81/1.01  --clause_weak_htbl                      true
% 0.81/1.01  --gc_record_bc_elim                     false
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing Options
% 0.81/1.01  
% 0.81/1.01  --preprocessing_flag                    true
% 0.81/1.01  --time_out_prep_mult                    0.1
% 0.81/1.01  --splitting_mode                        input
% 0.81/1.01  --splitting_grd                         true
% 0.81/1.01  --splitting_cvd                         false
% 0.81/1.01  --splitting_cvd_svl                     false
% 0.81/1.01  --splitting_nvd                         32
% 0.81/1.01  --sub_typing                            true
% 0.81/1.01  --prep_gs_sim                           true
% 0.81/1.01  --prep_unflatten                        true
% 0.81/1.01  --prep_res_sim                          true
% 0.81/1.01  --prep_upred                            true
% 0.81/1.01  --prep_sem_filter                       exhaustive
% 0.81/1.01  --prep_sem_filter_out                   false
% 0.81/1.01  --pred_elim                             true
% 0.81/1.01  --res_sim_input                         true
% 0.81/1.01  --eq_ax_congr_red                       true
% 0.81/1.01  --pure_diseq_elim                       true
% 0.81/1.01  --brand_transform                       false
% 0.81/1.01  --non_eq_to_eq                          false
% 0.81/1.01  --prep_def_merge                        true
% 0.81/1.01  --prep_def_merge_prop_impl              false
% 0.81/1.01  --prep_def_merge_mbd                    true
% 0.81/1.01  --prep_def_merge_tr_red                 false
% 0.81/1.01  --prep_def_merge_tr_cl                  false
% 0.81/1.01  --smt_preprocessing                     true
% 0.81/1.01  --smt_ac_axioms                         fast
% 0.81/1.01  --preprocessed_out                      false
% 0.81/1.01  --preprocessed_stats                    false
% 0.81/1.01  
% 0.81/1.01  ------ Abstraction refinement Options
% 0.81/1.01  
% 0.81/1.01  --abstr_ref                             []
% 0.81/1.01  --abstr_ref_prep                        false
% 0.81/1.01  --abstr_ref_until_sat                   false
% 0.81/1.01  --abstr_ref_sig_restrict                funpre
% 0.81/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/1.01  --abstr_ref_under                       []
% 0.81/1.01  
% 0.81/1.01  ------ SAT Options
% 0.81/1.01  
% 0.81/1.01  --sat_mode                              false
% 0.81/1.01  --sat_fm_restart_options                ""
% 0.81/1.01  --sat_gr_def                            false
% 0.81/1.01  --sat_epr_types                         true
% 0.81/1.01  --sat_non_cyclic_types                  false
% 0.81/1.01  --sat_finite_models                     false
% 0.81/1.01  --sat_fm_lemmas                         false
% 0.81/1.01  --sat_fm_prep                           false
% 0.81/1.01  --sat_fm_uc_incr                        true
% 0.81/1.01  --sat_out_model                         small
% 0.81/1.01  --sat_out_clauses                       false
% 0.81/1.01  
% 0.81/1.01  ------ QBF Options
% 0.81/1.01  
% 0.81/1.01  --qbf_mode                              false
% 0.81/1.01  --qbf_elim_univ                         false
% 0.81/1.01  --qbf_dom_inst                          none
% 0.81/1.01  --qbf_dom_pre_inst                      false
% 0.81/1.01  --qbf_sk_in                             false
% 0.81/1.01  --qbf_pred_elim                         true
% 0.81/1.01  --qbf_split                             512
% 0.81/1.01  
% 0.81/1.01  ------ BMC1 Options
% 0.81/1.01  
% 0.81/1.01  --bmc1_incremental                      false
% 0.81/1.01  --bmc1_axioms                           reachable_all
% 0.81/1.01  --bmc1_min_bound                        0
% 0.81/1.01  --bmc1_max_bound                        -1
% 0.81/1.01  --bmc1_max_bound_default                -1
% 0.81/1.01  --bmc1_symbol_reachability              true
% 0.81/1.01  --bmc1_property_lemmas                  false
% 0.81/1.01  --bmc1_k_induction                      false
% 0.81/1.01  --bmc1_non_equiv_states                 false
% 0.81/1.01  --bmc1_deadlock                         false
% 0.81/1.01  --bmc1_ucm                              false
% 0.81/1.01  --bmc1_add_unsat_core                   none
% 0.81/1.01  --bmc1_unsat_core_children              false
% 0.81/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/1.01  --bmc1_out_stat                         full
% 0.81/1.01  --bmc1_ground_init                      false
% 0.81/1.01  --bmc1_pre_inst_next_state              false
% 0.81/1.01  --bmc1_pre_inst_state                   false
% 0.81/1.01  --bmc1_pre_inst_reach_state             false
% 0.81/1.01  --bmc1_out_unsat_core                   false
% 0.81/1.01  --bmc1_aig_witness_out                  false
% 0.81/1.01  --bmc1_verbose                          false
% 0.81/1.01  --bmc1_dump_clauses_tptp                false
% 0.81/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.81/1.01  --bmc1_dump_file                        -
% 0.81/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.81/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.81/1.01  --bmc1_ucm_extend_mode                  1
% 0.81/1.01  --bmc1_ucm_init_mode                    2
% 0.81/1.01  --bmc1_ucm_cone_mode                    none
% 0.81/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.81/1.01  --bmc1_ucm_relax_model                  4
% 0.81/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.81/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/1.01  --bmc1_ucm_layered_model                none
% 0.81/1.01  --bmc1_ucm_max_lemma_size               10
% 0.81/1.01  
% 0.81/1.01  ------ AIG Options
% 0.81/1.01  
% 0.81/1.01  --aig_mode                              false
% 0.81/1.01  
% 0.81/1.01  ------ Instantiation Options
% 0.81/1.01  
% 0.81/1.01  --instantiation_flag                    true
% 0.81/1.01  --inst_sos_flag                         false
% 0.81/1.01  --inst_sos_phase                        true
% 0.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/1.01  --inst_lit_sel_side                     none
% 0.81/1.01  --inst_solver_per_active                1400
% 0.81/1.01  --inst_solver_calls_frac                1.
% 0.81/1.01  --inst_passive_queue_type               priority_queues
% 0.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/1.01  --inst_passive_queues_freq              [25;2]
% 0.81/1.01  --inst_dismatching                      true
% 0.81/1.01  --inst_eager_unprocessed_to_passive     true
% 0.81/1.01  --inst_prop_sim_given                   true
% 0.81/1.01  --inst_prop_sim_new                     false
% 0.81/1.01  --inst_subs_new                         false
% 0.81/1.01  --inst_eq_res_simp                      false
% 0.81/1.01  --inst_subs_given                       false
% 0.81/1.01  --inst_orphan_elimination               true
% 0.81/1.01  --inst_learning_loop_flag               true
% 0.81/1.01  --inst_learning_start                   3000
% 0.81/1.01  --inst_learning_factor                  2
% 0.81/1.01  --inst_start_prop_sim_after_learn       3
% 0.81/1.01  --inst_sel_renew                        solver
% 0.81/1.01  --inst_lit_activity_flag                true
% 0.81/1.01  --inst_restr_to_given                   false
% 0.81/1.01  --inst_activity_threshold               500
% 0.81/1.01  --inst_out_proof                        true
% 0.81/1.01  
% 0.81/1.01  ------ Resolution Options
% 0.81/1.01  
% 0.81/1.01  --resolution_flag                       false
% 0.81/1.01  --res_lit_sel                           adaptive
% 0.81/1.01  --res_lit_sel_side                      none
% 0.81/1.01  --res_ordering                          kbo
% 0.81/1.01  --res_to_prop_solver                    active
% 0.81/1.01  --res_prop_simpl_new                    false
% 0.81/1.01  --res_prop_simpl_given                  true
% 0.81/1.01  --res_passive_queue_type                priority_queues
% 0.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/1.01  --res_passive_queues_freq               [15;5]
% 0.81/1.01  --res_forward_subs                      full
% 0.81/1.01  --res_backward_subs                     full
% 0.81/1.01  --res_forward_subs_resolution           true
% 0.81/1.01  --res_backward_subs_resolution          true
% 0.81/1.01  --res_orphan_elimination                true
% 0.81/1.01  --res_time_limit                        2.
% 0.81/1.01  --res_out_proof                         true
% 0.81/1.01  
% 0.81/1.01  ------ Superposition Options
% 0.81/1.01  
% 0.81/1.01  --superposition_flag                    true
% 0.81/1.01  --sup_passive_queue_type                priority_queues
% 0.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.81/1.01  --demod_completeness_check              fast
% 0.81/1.01  --demod_use_ground                      true
% 0.81/1.01  --sup_to_prop_solver                    passive
% 0.81/1.01  --sup_prop_simpl_new                    true
% 0.81/1.01  --sup_prop_simpl_given                  true
% 0.81/1.01  --sup_fun_splitting                     false
% 0.81/1.01  --sup_smt_interval                      50000
% 0.81/1.01  
% 0.81/1.01  ------ Superposition Simplification Setup
% 0.81/1.01  
% 0.81/1.01  --sup_indices_passive                   []
% 0.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_full_bw                           [BwDemod]
% 0.81/1.01  --sup_immed_triv                        [TrivRules]
% 0.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_immed_bw_main                     []
% 0.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/1.01  
% 0.81/1.01  ------ Combination Options
% 0.81/1.01  
% 0.81/1.01  --comb_res_mult                         3
% 0.81/1.01  --comb_sup_mult                         2
% 0.81/1.01  --comb_inst_mult                        10
% 0.81/1.01  
% 0.81/1.01  ------ Debug Options
% 0.81/1.01  
% 0.81/1.01  --dbg_backtrace                         false
% 0.81/1.01  --dbg_dump_prop_clauses                 false
% 0.81/1.01  --dbg_dump_prop_clauses_file            -
% 0.81/1.01  --dbg_out_stat                          false
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  ------ Proving...
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  % SZS status Theorem for theBenchmark.p
% 0.81/1.01  
% 0.81/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.81/1.01  
% 0.81/1.01  fof(f1,axiom,(
% 0.81/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f20,plain,(
% 0.81/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.81/1.01    inference(nnf_transformation,[],[f1])).
% 0.81/1.01  
% 0.81/1.01  fof(f21,plain,(
% 0.81/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.81/1.01    inference(flattening,[],[f20])).
% 0.81/1.01  
% 0.81/1.01  fof(f31,plain,(
% 0.81/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f21])).
% 0.81/1.01  
% 0.81/1.01  fof(f4,axiom,(
% 0.81/1.01    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f9,plain,(
% 0.81/1.01    ! [X0] : (! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => v2_ordinal1(X0))),
% 0.81/1.01    inference(unused_predicate_definition_removal,[],[f4])).
% 0.81/1.01  
% 0.81/1.01  fof(f14,plain,(
% 0.81/1.01    ! [X0] : (v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.81/1.01    inference(ennf_transformation,[],[f9])).
% 0.81/1.01  
% 0.81/1.01  fof(f24,plain,(
% 0.81/1.01    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.81/1.01    introduced(choice_axiom,[])).
% 0.81/1.01  
% 0.81/1.01  fof(f25,plain,(
% 0.81/1.01    ! [X0] : (v2_ordinal1(X0) | (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f24])).
% 0.81/1.01  
% 0.81/1.01  fof(f35,plain,(
% 0.81/1.01    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f25])).
% 0.81/1.01  
% 0.81/1.01  fof(f7,conjecture,(
% 0.81/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f8,negated_conjecture,(
% 0.81/1.01    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.81/1.01    inference(negated_conjecture,[],[f7])).
% 0.81/1.01  
% 0.81/1.01  fof(f19,plain,(
% 0.81/1.01    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 0.81/1.01    inference(ennf_transformation,[],[f8])).
% 0.81/1.01  
% 0.81/1.01  fof(f27,plain,(
% 0.81/1.01    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK3) & ! [X1] : ((r1_tarski(X1,sK3) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK3)))),
% 0.81/1.01    introduced(choice_axiom,[])).
% 0.81/1.01  
% 0.81/1.01  fof(f28,plain,(
% 0.81/1.01    ~v3_ordinal1(sK3) & ! [X1] : ((r1_tarski(X1,sK3) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK3))),
% 0.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).
% 0.81/1.01  
% 0.81/1.01  fof(f43,plain,(
% 0.81/1.01    ( ! [X1] : (v3_ordinal1(X1) | ~r2_hidden(X1,sK3)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f28])).
% 0.81/1.01  
% 0.81/1.01  fof(f36,plain,(
% 0.81/1.01    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f25])).
% 0.81/1.01  
% 0.81/1.01  fof(f37,plain,(
% 0.81/1.01    ( ! [X0] : (v2_ordinal1(X0) | ~r2_hidden(sK1(X0),sK2(X0))) )),
% 0.81/1.01    inference(cnf_transformation,[],[f25])).
% 0.81/1.01  
% 0.81/1.01  fof(f6,axiom,(
% 0.81/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f17,plain,(
% 0.81/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.81/1.01    inference(ennf_transformation,[],[f6])).
% 0.81/1.01  
% 0.81/1.01  fof(f18,plain,(
% 0.81/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.81/1.01    inference(flattening,[],[f17])).
% 0.81/1.01  
% 0.81/1.01  fof(f42,plain,(
% 0.81/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f18])).
% 0.81/1.01  
% 0.81/1.01  fof(f5,axiom,(
% 0.81/1.01    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f15,plain,(
% 0.81/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.81/1.01    inference(ennf_transformation,[],[f5])).
% 0.81/1.01  
% 0.81/1.01  fof(f16,plain,(
% 0.81/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.81/1.01    inference(flattening,[],[f15])).
% 0.81/1.01  
% 0.81/1.01  fof(f26,plain,(
% 0.81/1.01    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.81/1.01    inference(nnf_transformation,[],[f16])).
% 0.81/1.01  
% 0.81/1.01  fof(f40,plain,(
% 0.81/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f26])).
% 0.81/1.01  
% 0.81/1.01  fof(f39,plain,(
% 0.81/1.01    ( ! [X0] : (v2_ordinal1(X0) | ~r2_hidden(sK2(X0),sK1(X0))) )),
% 0.81/1.01    inference(cnf_transformation,[],[f25])).
% 0.81/1.01  
% 0.81/1.01  fof(f3,axiom,(
% 0.81/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f10,plain,(
% 0.81/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)) => v1_ordinal1(X0))),
% 0.81/1.01    inference(unused_predicate_definition_removal,[],[f3])).
% 0.81/1.01  
% 0.81/1.01  fof(f13,plain,(
% 0.81/1.01    ! [X0] : (v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)))),
% 0.81/1.01    inference(ennf_transformation,[],[f10])).
% 0.81/1.01  
% 0.81/1.01  fof(f22,plain,(
% 0.81/1.01    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0)))),
% 0.81/1.01    introduced(choice_axiom,[])).
% 0.81/1.01  
% 0.81/1.01  fof(f23,plain,(
% 0.81/1.01    ! [X0] : (v1_ordinal1(X0) | (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0)))),
% 0.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).
% 0.81/1.01  
% 0.81/1.01  fof(f33,plain,(
% 0.81/1.01    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f23])).
% 0.81/1.01  
% 0.81/1.01  fof(f44,plain,(
% 0.81/1.01    ( ! [X1] : (r1_tarski(X1,sK3) | ~r2_hidden(X1,sK3)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f28])).
% 0.81/1.01  
% 0.81/1.01  fof(f34,plain,(
% 0.81/1.01    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK0(X0),X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f23])).
% 0.81/1.01  
% 0.81/1.01  fof(f38,plain,(
% 0.81/1.01    ( ! [X0] : (v2_ordinal1(X0) | sK1(X0) != sK2(X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f25])).
% 0.81/1.01  
% 0.81/1.01  fof(f2,axiom,(
% 0.81/1.01    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 0.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/1.01  
% 0.81/1.01  fof(f11,plain,(
% 0.81/1.01    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 0.81/1.01    inference(ennf_transformation,[],[f2])).
% 0.81/1.01  
% 0.81/1.01  fof(f12,plain,(
% 0.81/1.01    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 0.81/1.01    inference(flattening,[],[f11])).
% 0.81/1.01  
% 0.81/1.01  fof(f32,plain,(
% 0.81/1.01    ( ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 0.81/1.01    inference(cnf_transformation,[],[f12])).
% 0.81/1.01  
% 0.81/1.01  fof(f45,plain,(
% 0.81/1.01    ~v3_ordinal1(sK3)),
% 0.81/1.01    inference(cnf_transformation,[],[f28])).
% 0.81/1.01  
% 0.81/1.01  cnf(c_0,plain,
% 0.81/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.81/1.01      inference(cnf_transformation,[],[f31]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_1356,plain,
% 0.81/1.01      ( ~ r1_tarski(sK1(X0),sK2(X0))
% 0.81/1.01      | ~ r1_tarski(sK2(X0),sK1(X0))
% 0.81/1.01      | sK1(X0) = sK2(X0) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_1358,plain,
% 0.81/1.01      ( ~ r1_tarski(sK1(sK3),sK2(sK3))
% 0.81/1.01      | ~ r1_tarski(sK2(sK3),sK1(sK3))
% 0.81/1.01      | sK1(sK3) = sK2(sK3) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_1356]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_10,plain,
% 0.81/1.01      ( r2_hidden(sK1(X0),X0) | v2_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f35]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_16,negated_conjecture,
% 0.81/1.01      ( ~ r2_hidden(X0,sK3) | v3_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f43]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_497,plain,
% 0.81/1.01      ( v2_ordinal1(X0) | v3_ordinal1(X1) | sK1(X0) != X1 | sK3 != X0 ),
% 0.81/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_498,plain,
% 0.81/1.01      ( v2_ordinal1(sK3) | v3_ordinal1(sK1(sK3)) ),
% 0.81/1.01      inference(unflattening,[status(thm)],[c_497]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_9,plain,
% 0.81/1.01      ( r2_hidden(sK2(X0),X0) | v2_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f36]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_475,plain,
% 0.81/1.01      ( v2_ordinal1(X0) | v3_ordinal1(X1) | sK2(X0) != X1 | sK3 != X0 ),
% 0.81/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_476,plain,
% 0.81/1.01      ( v2_ordinal1(sK3) | v3_ordinal1(sK2(sK3)) ),
% 0.81/1.01      inference(unflattening,[status(thm)],[c_475]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_8,plain,
% 0.81/1.01      ( ~ r2_hidden(sK1(X0),sK2(X0)) | v2_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f37]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_13,plain,
% 0.81/1.01      ( r1_ordinal1(X0,X1)
% 0.81/1.01      | r2_hidden(X1,X0)
% 0.81/1.01      | ~ v3_ordinal1(X1)
% 0.81/1.01      | ~ v3_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f42]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_12,plain,
% 0.81/1.01      ( ~ r1_ordinal1(X0,X1)
% 0.81/1.01      | r1_tarski(X0,X1)
% 0.81/1.01      | ~ v3_ordinal1(X1)
% 0.81/1.01      | ~ v3_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f40]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_222,plain,
% 0.81/1.01      ( r2_hidden(X0,X1)
% 0.81/1.01      | r1_tarski(X1,X0)
% 0.81/1.01      | ~ v3_ordinal1(X1)
% 0.81/1.01      | ~ v3_ordinal1(X0) ),
% 0.81/1.01      inference(resolution,[status(thm)],[c_13,c_12]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_457,plain,
% 0.81/1.01      ( r1_tarski(X0,X1)
% 0.81/1.01      | v2_ordinal1(X2)
% 0.81/1.01      | ~ v3_ordinal1(X1)
% 0.81/1.01      | ~ v3_ordinal1(X0)
% 0.81/1.01      | sK1(X2) != X1
% 0.81/1.01      | sK2(X2) != X0 ),
% 0.81/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_222]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_458,plain,
% 0.81/1.01      ( r1_tarski(sK2(X0),sK1(X0))
% 0.81/1.01      | v2_ordinal1(X0)
% 0.81/1.01      | ~ v3_ordinal1(sK1(X0))
% 0.81/1.01      | ~ v3_ordinal1(sK2(X0)) ),
% 0.81/1.01      inference(unflattening,[status(thm)],[c_457]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_460,plain,
% 0.81/1.01      ( r1_tarski(sK2(sK3),sK1(sK3))
% 0.81/1.01      | v2_ordinal1(sK3)
% 0.81/1.01      | ~ v3_ordinal1(sK1(sK3))
% 0.81/1.01      | ~ v3_ordinal1(sK2(sK3)) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_458]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_6,plain,
% 0.81/1.01      ( ~ r2_hidden(sK2(X0),sK1(X0)) | v2_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_409,plain,
% 0.81/1.01      ( r1_tarski(X0,X1)
% 0.81/1.01      | v2_ordinal1(X2)
% 0.81/1.01      | ~ v3_ordinal1(X1)
% 0.81/1.01      | ~ v3_ordinal1(X0)
% 0.81/1.01      | sK1(X2) != X0
% 0.81/1.01      | sK2(X2) != X1 ),
% 0.81/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_222]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_410,plain,
% 0.81/1.01      ( r1_tarski(sK1(X0),sK2(X0))
% 0.81/1.01      | v2_ordinal1(X0)
% 0.81/1.01      | ~ v3_ordinal1(sK1(X0))
% 0.81/1.01      | ~ v3_ordinal1(sK2(X0)) ),
% 0.81/1.01      inference(unflattening,[status(thm)],[c_409]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_412,plain,
% 0.81/1.01      ( r1_tarski(sK1(sK3),sK2(sK3))
% 0.81/1.01      | v2_ordinal1(sK3)
% 0.81/1.01      | ~ v3_ordinal1(sK1(sK3))
% 0.81/1.01      | ~ v3_ordinal1(sK2(sK3)) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_410]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_5,plain,
% 0.81/1.01      ( r2_hidden(sK0(X0),X0) | v1_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f33]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_15,negated_conjecture,
% 0.81/1.01      ( ~ r2_hidden(X0,sK3) | r1_tarski(X0,sK3) ),
% 0.81/1.01      inference(cnf_transformation,[],[f44]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_368,plain,
% 0.81/1.01      ( r1_tarski(X0,sK3) | v1_ordinal1(X1) | sK0(X1) != X0 | sK3 != X1 ),
% 0.81/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_369,plain,
% 0.81/1.01      ( r1_tarski(sK0(sK3),sK3) | v1_ordinal1(sK3) ),
% 0.81/1.01      inference(unflattening,[status(thm)],[c_368]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_4,plain,
% 0.81/1.01      ( ~ r1_tarski(sK0(X0),X0) | v1_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f34]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_46,plain,
% 0.81/1.01      ( ~ r1_tarski(sK0(sK3),sK3) | v1_ordinal1(sK3) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_371,plain,
% 0.81/1.01      ( v1_ordinal1(sK3) ),
% 0.81/1.01      inference(global_propositional_subsumption,
% 0.81/1.01                [status(thm)],
% 0.81/1.01                [c_369,c_46]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_7,plain,
% 0.81/1.01      ( v2_ordinal1(X0) | sK1(X0) != sK2(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f38]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_3,plain,
% 0.81/1.01      ( ~ v1_ordinal1(X0) | ~ v2_ordinal1(X0) | v3_ordinal1(X0) ),
% 0.81/1.01      inference(cnf_transformation,[],[f32]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_285,plain,
% 0.81/1.01      ( ~ v1_ordinal1(X0) | v3_ordinal1(X0) | sK1(X0) != sK2(X0) ),
% 0.81/1.01      inference(resolution,[status(thm)],[c_7,c_3]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_287,plain,
% 0.81/1.01      ( ~ v1_ordinal1(sK3) | v3_ordinal1(sK3) | sK1(sK3) != sK2(sK3) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_285]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_49,plain,
% 0.81/1.01      ( ~ v1_ordinal1(sK3) | ~ v2_ordinal1(sK3) | v3_ordinal1(sK3) ),
% 0.81/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(c_14,negated_conjecture,
% 0.81/1.01      ( ~ v3_ordinal1(sK3) ),
% 0.81/1.01      inference(cnf_transformation,[],[f45]) ).
% 0.81/1.01  
% 0.81/1.01  cnf(contradiction,plain,
% 0.81/1.01      ( $false ),
% 0.81/1.01      inference(minisat,
% 0.81/1.01                [status(thm)],
% 0.81/1.01                [c_1358,c_498,c_476,c_460,c_412,c_371,c_287,c_49,c_14]) ).
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.81/1.01  
% 0.81/1.01  ------                               Statistics
% 0.81/1.01  
% 0.81/1.01  ------ General
% 0.81/1.01  
% 0.81/1.01  abstr_ref_over_cycles:                  0
% 0.81/1.01  abstr_ref_under_cycles:                 0
% 0.81/1.01  gc_basic_clause_elim:                   0
% 0.81/1.01  forced_gc_time:                         0
% 0.81/1.01  parsing_time:                           0.007
% 0.81/1.01  unif_index_cands_time:                  0.
% 0.81/1.01  unif_index_add_time:                    0.
% 0.81/1.01  orderings_time:                         0.
% 0.81/1.01  out_proof_time:                         0.008
% 0.81/1.01  total_time:                             0.057
% 0.81/1.01  num_of_symbols:                         38
% 0.81/1.01  num_of_terms:                           438
% 0.81/1.01  
% 0.81/1.01  ------ Preprocessing
% 0.81/1.01  
% 0.81/1.01  num_of_splits:                          0
% 0.81/1.01  num_of_split_atoms:                     0
% 0.81/1.01  num_of_reused_defs:                     0
% 0.81/1.01  num_eq_ax_congr_red:                    17
% 0.81/1.01  num_of_sem_filtered_clauses:            1
% 0.81/1.01  num_of_subtypes:                        0
% 0.81/1.01  monotx_restored_types:                  0
% 0.81/1.01  sat_num_of_epr_types:                   0
% 0.81/1.01  sat_num_of_non_cyclic_types:            0
% 0.81/1.01  sat_guarded_non_collapsed_types:        0
% 0.81/1.01  num_pure_diseq_elim:                    0
% 0.81/1.01  simp_replaced_by:                       0
% 0.81/1.01  res_preprocessed:                       69
% 0.81/1.01  prep_upred:                             0
% 0.81/1.01  prep_unflattend:                        52
% 0.81/1.01  smt_new_axioms:                         0
% 0.81/1.01  pred_elim_cands:                        5
% 0.81/1.01  pred_elim:                              1
% 0.81/1.01  pred_elim_cl:                           2
% 0.81/1.01  pred_elim_cycles:                       7
% 0.81/1.01  merged_defs:                            0
% 0.81/1.01  merged_defs_ncl:                        0
% 0.81/1.01  bin_hyper_res:                          0
% 0.81/1.01  prep_cycles:                            4
% 0.81/1.01  pred_elim_time:                         0.008
% 0.81/1.01  splitting_time:                         0.
% 0.81/1.01  sem_filter_time:                        0.
% 0.81/1.01  monotx_time:                            0.001
% 0.81/1.01  subtype_inf_time:                       0.
% 0.81/1.01  
% 0.81/1.01  ------ Problem properties
% 0.81/1.01  
% 0.81/1.01  clauses:                                14
% 0.81/1.01  conjectures:                            3
% 0.81/1.01  epr:                                    7
% 0.81/1.01  horn:                                   10
% 0.81/1.01  ground:                                 1
% 0.81/1.01  unary:                                  2
% 0.81/1.01  binary:                                 9
% 0.81/1.01  lits:                                   30
% 0.81/1.01  lits_eq:                                2
% 0.81/1.01  fd_pure:                                0
% 0.81/1.01  fd_pseudo:                              0
% 0.81/1.01  fd_cond:                                0
% 0.81/1.01  fd_pseudo_cond:                         1
% 0.81/1.01  ac_symbols:                             0
% 0.81/1.01  
% 0.81/1.01  ------ Propositional Solver
% 0.81/1.01  
% 0.81/1.01  prop_solver_calls:                      22
% 0.81/1.01  prop_fast_solver_calls:                 452
% 0.81/1.01  smt_solver_calls:                       0
% 0.81/1.01  smt_fast_solver_calls:                  0
% 0.81/1.01  prop_num_of_clauses:                    161
% 0.81/1.01  prop_preprocess_simplified:             2310
% 0.81/1.01  prop_fo_subsumed:                       10
% 0.81/1.01  prop_solver_time:                       0.
% 0.81/1.01  smt_solver_time:                        0.
% 0.81/1.01  smt_fast_solver_time:                   0.
% 0.81/1.01  prop_fast_solver_time:                  0.
% 0.81/1.01  prop_unsat_core_time:                   0.
% 0.81/1.01  
% 0.81/1.01  ------ QBF
% 0.81/1.01  
% 0.81/1.01  qbf_q_res:                              0
% 0.81/1.01  qbf_num_tautologies:                    0
% 0.81/1.01  qbf_prep_cycles:                        0
% 0.81/1.01  
% 0.81/1.01  ------ BMC1
% 0.81/1.01  
% 0.81/1.01  bmc1_current_bound:                     -1
% 0.81/1.01  bmc1_last_solved_bound:                 -1
% 0.81/1.01  bmc1_unsat_core_size:                   -1
% 0.81/1.01  bmc1_unsat_core_parents_size:           -1
% 0.81/1.01  bmc1_merge_next_fun:                    0
% 0.81/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.81/1.01  
% 0.81/1.01  ------ Instantiation
% 0.81/1.01  
% 0.81/1.01  inst_num_of_clauses:                    25
% 0.81/1.01  inst_num_in_passive:                    1
% 0.81/1.01  inst_num_in_active:                     17
% 0.81/1.01  inst_num_in_unprocessed:                6
% 0.81/1.01  inst_num_of_loops:                      18
% 0.81/1.01  inst_num_of_learning_restarts:          0
% 0.81/1.01  inst_num_moves_active_passive:          0
% 0.81/1.01  inst_lit_activity:                      0
% 0.81/1.01  inst_lit_activity_moves:                0
% 0.81/1.01  inst_num_tautologies:                   0
% 0.81/1.01  inst_num_prop_implied:                  0
% 0.81/1.01  inst_num_existing_simplified:           0
% 0.81/1.01  inst_num_eq_res_simplified:             0
% 0.81/1.01  inst_num_child_elim:                    0
% 0.81/1.01  inst_num_of_dismatching_blockings:      0
% 0.81/1.01  inst_num_of_non_proper_insts:           3
% 0.81/1.01  inst_num_of_duplicates:                 0
% 0.81/1.01  inst_inst_num_from_inst_to_res:         0
% 0.81/1.01  inst_dismatching_checking_time:         0.
% 0.81/1.01  
% 0.81/1.01  ------ Resolution
% 0.81/1.01  
% 0.81/1.01  res_num_of_clauses:                     0
% 0.81/1.01  res_num_in_passive:                     0
% 0.81/1.01  res_num_in_active:                      0
% 0.81/1.01  res_num_of_loops:                       73
% 0.81/1.01  res_forward_subset_subsumed:            3
% 0.81/1.01  res_backward_subset_subsumed:           1
% 0.81/1.01  res_forward_subsumed:                   0
% 0.81/1.01  res_backward_subsumed:                  0
% 0.81/1.01  res_forward_subsumption_resolution:     0
% 0.81/1.01  res_backward_subsumption_resolution:    0
% 0.81/1.01  res_clause_to_clause_subsumption:       93
% 0.81/1.01  res_orphan_elimination:                 0
% 0.81/1.01  res_tautology_del:                      3
% 0.81/1.01  res_num_eq_res_simplified:              0
% 0.81/1.01  res_num_sel_changes:                    0
% 0.81/1.01  res_moves_from_active_to_pass:          0
% 0.81/1.01  
% 0.81/1.01  ------ Superposition
% 0.81/1.01  
% 0.81/1.01  sup_time_total:                         0.
% 0.81/1.01  sup_time_generating:                    0.
% 0.81/1.01  sup_time_sim_full:                      0.
% 0.81/1.01  sup_time_sim_immed:                     0.
% 0.81/1.01  
% 0.81/1.01  sup_num_of_clauses:                     14
% 0.81/1.01  sup_num_in_active:                      2
% 0.81/1.01  sup_num_in_passive:                     12
% 0.81/1.01  sup_num_of_loops:                       2
% 0.81/1.01  sup_fw_superposition:                   0
% 0.81/1.01  sup_bw_superposition:                   0
% 0.81/1.01  sup_immediate_simplified:               0
% 0.81/1.01  sup_given_eliminated:                   0
% 0.81/1.01  comparisons_done:                       0
% 0.81/1.01  comparisons_avoided:                    0
% 0.81/1.01  
% 0.81/1.01  ------ Simplifications
% 0.81/1.01  
% 0.81/1.01  
% 0.81/1.01  sim_fw_subset_subsumed:                 0
% 0.81/1.01  sim_bw_subset_subsumed:                 0
% 0.81/1.01  sim_fw_subsumed:                        0
% 0.81/1.01  sim_bw_subsumed:                        0
% 0.81/1.01  sim_fw_subsumption_res:                 0
% 0.81/1.01  sim_bw_subsumption_res:                 0
% 0.81/1.01  sim_tautology_del:                      0
% 0.81/1.01  sim_eq_tautology_del:                   0
% 0.81/1.01  sim_eq_res_simp:                        0
% 0.81/1.01  sim_fw_demodulated:                     0
% 0.81/1.01  sim_bw_demodulated:                     0
% 0.81/1.01  sim_light_normalised:                   0
% 0.81/1.01  sim_joinable_taut:                      0
% 0.81/1.01  sim_joinable_simp:                      0
% 0.81/1.01  sim_ac_normalised:                      0
% 0.81/1.01  sim_smt_subsumption:                    0
% 0.81/1.01  
%------------------------------------------------------------------------------
