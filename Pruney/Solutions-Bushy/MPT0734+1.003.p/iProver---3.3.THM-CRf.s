%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0734+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:00 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 154 expanded)
%              Number of clauses        :   36 (  39 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  261 ( 747 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X1,X2)
          & r1_tarski(X0,X1)
          & v3_ordinal1(X2) )
     => ( ~ r2_hidden(X0,sK3)
        & r2_hidden(X1,sK3)
        & r1_tarski(X0,X1)
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(sK2,X2)
            & r1_tarski(X0,sK2)
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK1,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK1,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK3)
    & r2_hidden(sK2,sK3)
    & r1_tarski(sK1,sK2)
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2)
    & v1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f36,f35,f34])).

fof(f55,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2057,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2246,plain,
    ( m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_2248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | m1_subset_1(sK1,sK3)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_1375,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2176,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1954,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_712,plain,
    ( sK2 != sK1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_625,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_626,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_616,plain,
    ( ~ v1_xboole_0(X0)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_617,plain,
    ( ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK1,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_4,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_243,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_16,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_301,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_243,c_16])).

cnf(c_302,plain,
    ( r2_hidden(X0,sK2)
    | ~ r1_tarski(X0,sK2)
    | ~ v1_ordinal1(X0)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_17,negated_conjecture,
    ( v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_431,plain,
    ( r2_hidden(X0,sK2)
    | ~ r1_tarski(X0,sK2)
    | sK2 = X0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_302,c_17])).

cnf(c_432,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r1_tarski(sK1,sK2)
    | sK2 = sK1 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_434,plain,
    ( r2_hidden(sK1,sK2)
    | sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_14])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_269,plain,
    ( v1_ordinal1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_270,plain,
    ( v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2248,c_2176,c_1954,c_712,c_626,c_617,c_607,c_434,c_270])).


%------------------------------------------------------------------------------
