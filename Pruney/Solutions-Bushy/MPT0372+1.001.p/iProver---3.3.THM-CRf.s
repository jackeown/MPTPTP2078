%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:08 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  232 ( 616 expanded)
%              Number of equality atoms :   53 ( 105 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK3) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,sK3)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK1,X2) != sK2
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK2) ) )
              | ~ m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k3_subset_1(sK1,sK3) != sK2
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK3)
            | r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f14,f13])).

fof(f22,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X2)
          | ~ r2_hidden(sK0(X0,X1,X2),X1) )
        & ( ~ r2_hidden(sK0(X0,X1,X2),X2)
          | r2_hidden(sK0(X0,X1,X2),X1) )
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( r2_hidden(sK0(X0,X1,X2),X2)
              | ~ r2_hidden(sK0(X0,X1,X2),X1) )
            & ( ~ r2_hidden(sK0(X0,X1,X2),X2)
              | r2_hidden(sK0(X0,X1,X2),X1) )
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    k3_subset_1(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_80,negated_conjecture,
    ( ~ m1_subset_1(X0_36,sK1)
    | ~ r2_hidden(X0_36,sK2)
    | ~ r2_hidden(X0_36,sK3) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_314,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK3),sK1)
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK2)
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_318,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_5,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK2)
    | r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_79,negated_conjecture,
    ( ~ m1_subset_1(X0_36,sK1)
    | r2_hidden(X0_36,sK2)
    | r2_hidden(X0_36,sK3) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_315,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK3),sK1)
    | r2_hidden(sK0(sK1,sK2,sK3),sK2)
    | r2_hidden(sK0(sK1,sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_316,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X2)
    | r2_hidden(sK0(X1,X2,X0),X0)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_84,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(X1_36,k1_zfmisc_1(X0_37))
    | ~ r2_hidden(sK0(X0_37,X1_36,X0_36),X1_36)
    | r2_hidden(sK0(X0_37,X1_36,X0_36),X0_36)
    | k3_subset_1(X0_37,X0_36) = X1_36 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK2)
    | r2_hidden(sK0(sK1,sK2,sK3),sK3)
    | k3_subset_1(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_312,plain,
    ( k3_subset_1(sK1,sK3) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_83,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(X1_36,k1_zfmisc_1(X0_37))
    | ~ r2_hidden(sK0(X0_37,X1_36,X0_36),X0_36)
    | r2_hidden(sK0(X0_37,X1_36,X0_36),X1_36)
    | k3_subset_1(X0_37,X0_36) = X1_36 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_308,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK0(sK1,sK2,sK3),sK2)
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK3)
    | k3_subset_1(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_309,plain,
    ( k3_subset_1(sK1,sK3) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_82,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(X1_36,k1_zfmisc_1(X0_37))
    | m1_subset_1(sK0(X0_37,X1_36,X0_36),X0_37)
    | k3_subset_1(X0_37,X0_36) = X1_36 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_305,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_306,plain,
    ( k3_subset_1(sK1,sK3) = sK2
    | m1_subset_1(sK0(sK1,sK2,sK3),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_3,negated_conjecture,
    ( k3_subset_1(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_81,negated_conjecture,
    ( k3_subset_1(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_318,c_316,c_312,c_309,c_306,c_81,c_9,c_8])).


%------------------------------------------------------------------------------
