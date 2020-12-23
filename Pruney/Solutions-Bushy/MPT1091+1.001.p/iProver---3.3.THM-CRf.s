%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1091+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:52 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 199 expanded)
%              Number of clauses        :   23 (  43 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 735 expanded)
%              Number of equality atoms :    2 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( v1_finset_1(k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f21])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2)
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK1))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK1) )
        | ~ v1_finset_1(sK1) )
      & ( v1_finset_1(k3_tarski(sK1))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK1) )
          & v1_finset_1(sK1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK1))
      | ( ~ v1_finset_1(sK2)
        & r2_hidden(sK2,sK1) )
      | ~ v1_finset_1(sK1) )
    & ( v1_finset_1(k3_tarski(sK1))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK1) )
        & v1_finset_1(sK1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f24,f23])).

fof(f36,plain,
    ( ~ v1_finset_1(k3_tarski(sK1))
    | r2_hidden(sK2,sK1)
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,
    ( ~ v1_finset_1(k3_tarski(sK1))
    | ~ v1_finset_1(sK2)
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK0(X0))
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK0(X0))
        & r2_hidden(sK0(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f28,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | r2_hidden(sK0(X0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK1))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,
    ( v1_finset_1(k3_tarski(sK1))
    | v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK0(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] : r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(definition_unfolding,[],[f31,f30])).

cnf(c_1,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_247,plain,
    ( ~ v1_finset_1(k3_tarski(sK1))
    | v1_finset_1(k9_setfam_1(k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_0])).

cnf(c_6,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_142,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_finset_1(X0)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK2,sK1)
    | ~ v1_finset_1(k3_tarski(sK1))
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_178,plain,
    ( ~ v1_finset_1(k3_tarski(sK1))
    | v1_finset_1(sK2)
    | ~ v1_finset_1(sK1) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

cnf(c_7,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(sK1))
    | ~ v1_finset_1(sK2)
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | ~ v1_finset_1(X0)
    | v1_finset_1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | v1_finset_1(X0)
    | v1_finset_1(k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_162,plain,
    ( ~ r2_hidden(X0,sK1)
    | v1_finset_1(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_142,c_9])).

cnf(c_168,plain,
    ( v1_finset_1(sK0(sK1))
    | v1_finset_1(k3_tarski(sK1))
    | ~ v1_finset_1(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_162])).

cnf(c_10,negated_conjecture,
    ( v1_finset_1(k3_tarski(sK1))
    | v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ v1_finset_1(X0)
    | ~ v1_finset_1(sK0(X0))
    | v1_finset_1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_28,plain,
    ( ~ v1_finset_1(sK0(sK1))
    | v1_finset_1(k3_tarski(sK1))
    | ~ v1_finset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_170,plain,
    ( v1_finset_1(k3_tarski(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_168,c_10,c_28])).

cnf(c_180,plain,
    ( ~ v1_finset_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_10,c_7,c_28,c_168])).

cnf(c_4,plain,
    ( r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_131,plain,
    ( v1_finset_1(X0)
    | ~ v1_finset_1(k9_setfam_1(k3_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

cnf(c_133,plain,
    ( ~ v1_finset_1(k9_setfam_1(k3_tarski(sK1)))
    | v1_finset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_247,c_180,c_170,c_133])).


%------------------------------------------------------------------------------
