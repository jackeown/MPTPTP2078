%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0343+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 140 expanded)
%              Number of clauses        :   27 (  37 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 ( 832 expanded)
%              Number of equality atoms :   73 ( 147 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f706,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f707,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f706])).

fof(f920,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK66(X0,X1,X2),X2)
        & r2_hidden(sK66(X0,X1,X2),X1)
        & m1_subset_1(sK66(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f921,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK66(X0,X1,X2),X2)
            & r2_hidden(sK66(X0,X1,X2),X1)
            & m1_subset_1(sK66(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66])],[f707,f920])).

fof(f1601,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK66(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f921])).

fof(f1600,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK66(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f921])).

fof(f463,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f464,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f463])).

fof(f708,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f464])).

fof(f709,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f708])).

fof(f922,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f709])).

fof(f924,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK69 != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK69) )
              & ( r2_hidden(X3,sK69)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK69,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f923,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK68 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK68)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK68) ) )
              | ~ m1_subset_1(X3,sK67) )
          & m1_subset_1(X2,k1_zfmisc_1(sK67)) )
      & m1_subset_1(sK68,k1_zfmisc_1(sK67)) ) ),
    introduced(choice_axiom,[])).

fof(f925,plain,
    ( sK68 != sK69
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK68)
            | ~ r2_hidden(X3,sK69) )
          & ( r2_hidden(X3,sK69)
            | ~ r2_hidden(X3,sK68) ) )
        | ~ m1_subset_1(X3,sK67) )
    & m1_subset_1(sK69,k1_zfmisc_1(sK67))
    & m1_subset_1(sK68,k1_zfmisc_1(sK67)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK67,sK68,sK69])],[f922,f924,f923])).

fof(f1605,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK69)
      | ~ r2_hidden(X3,sK68)
      | ~ m1_subset_1(X3,sK67) ) ),
    inference(cnf_transformation,[],[f925])).

fof(f1603,plain,(
    m1_subset_1(sK68,k1_zfmisc_1(sK67)) ),
    inference(cnf_transformation,[],[f925])).

fof(f1602,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK66(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f921])).

fof(f1606,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK68)
      | ~ r2_hidden(X3,sK69)
      | ~ m1_subset_1(X3,sK67) ) ),
    inference(cnf_transformation,[],[f925])).

fof(f1604,plain,(
    m1_subset_1(sK69,k1_zfmisc_1(sK67)) ),
    inference(cnf_transformation,[],[f925])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f761,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f762,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f761])).

fof(f994,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f762])).

fof(f1607,plain,(
    sK68 != sK69 ),
    inference(cnf_transformation,[],[f925])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | r2_hidden(sK66(X1,X0,X2),X0) ),
    inference(cnf_transformation,[],[f1601])).

cnf(c_19574,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r2_hidden(sK66(X1,X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK66(X1,X0,X2),X1)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1600])).

cnf(c_19573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK66(X1,X0,X2),X1) = iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_666,negated_conjecture,
    ( ~ m1_subset_1(X0,sK67)
    | r2_hidden(X0,sK69)
    | ~ r2_hidden(X0,sK68) ),
    inference(cnf_transformation,[],[f1605])).

cnf(c_19571,plain,
    ( m1_subset_1(X0,sK67) != iProver_top
    | r2_hidden(X0,sK69) = iProver_top
    | r2_hidden(X0,sK68) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_25236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK66(sK67,X0,X1),sK69) = iProver_top
    | r2_hidden(sK66(sK67,X0,X1),sK68) != iProver_top ),
    inference(superposition,[status(thm)],[c_19573,c_19571])).

cnf(c_27021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(sK68,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK68,X0) = iProver_top
    | r2_hidden(sK66(sK67,sK68,X0),sK69) = iProver_top ),
    inference(superposition,[status(thm)],[c_19574,c_25236])).

cnf(c_668,negated_conjecture,
    ( m1_subset_1(sK68,k1_zfmisc_1(sK67)) ),
    inference(cnf_transformation,[],[f1603])).

cnf(c_669,plain,
    ( m1_subset_1(sK68,k1_zfmisc_1(sK67)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_28173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK68,X0) = iProver_top
    | r2_hidden(sK66(sK67,sK68,X0),sK69) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27021,c_669])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r2_hidden(sK66(X1,X0,X2),X2) ),
    inference(cnf_transformation,[],[f1602])).

cnf(c_19575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r2_hidden(sK66(X1,X0,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_29082,plain,
    ( m1_subset_1(sK69,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(sK68,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK68,sK69) = iProver_top ),
    inference(superposition,[status(thm)],[c_28173,c_19575])).

cnf(c_665,negated_conjecture,
    ( ~ m1_subset_1(X0,sK67)
    | ~ r2_hidden(X0,sK69)
    | r2_hidden(X0,sK68) ),
    inference(cnf_transformation,[],[f1606])).

cnf(c_19572,plain,
    ( m1_subset_1(X0,sK67) != iProver_top
    | r2_hidden(X0,sK69) != iProver_top
    | r2_hidden(X0,sK68) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_25235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK66(sK67,X0,X1),sK69) != iProver_top
    | r2_hidden(sK66(sK67,X0,X1),sK68) = iProver_top ),
    inference(superposition,[status(thm)],[c_19573,c_19572])).

cnf(c_27020,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(sK69,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK69,X0) = iProver_top
    | r2_hidden(sK66(sK67,sK69,X0),sK68) = iProver_top ),
    inference(superposition,[status(thm)],[c_19574,c_25235])).

cnf(c_667,negated_conjecture,
    ( m1_subset_1(sK69,k1_zfmisc_1(sK67)) ),
    inference(cnf_transformation,[],[f1604])).

cnf(c_670,plain,
    ( m1_subset_1(sK69,k1_zfmisc_1(sK67)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_28148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK69,X0) = iProver_top
    | r2_hidden(sK66(sK67,sK69,X0),sK68) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27020,c_670])).

cnf(c_29081,plain,
    ( m1_subset_1(sK69,k1_zfmisc_1(sK67)) != iProver_top
    | m1_subset_1(sK68,k1_zfmisc_1(sK67)) != iProver_top
    | r1_tarski(sK69,sK68) = iProver_top ),
    inference(superposition,[status(thm)],[c_28148,c_19575])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f994])).

cnf(c_24315,plain,
    ( ~ r1_tarski(sK69,sK68)
    | ~ r1_tarski(sK68,sK69)
    | sK68 = sK69 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_24316,plain,
    ( sK68 = sK69
    | r1_tarski(sK69,sK68) != iProver_top
    | r1_tarski(sK68,sK69) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24315])).

cnf(c_664,negated_conjecture,
    ( sK68 != sK69 ),
    inference(cnf_transformation,[],[f1607])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29082,c_29081,c_24316,c_664,c_670,c_669])).

%------------------------------------------------------------------------------
