%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0371+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 11.96s
% Output     : CNFRefutation 11.96s
% Verified   : 
% Statistics : Number of formulae       :   44 (  90 expanded)
%              Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  211 ( 595 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f514,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f513])).

fof(f826,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f514])).

fof(f827,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f826])).

fof(f1073,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f827])).

fof(f1075,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK76) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK76) )
              & ( r2_hidden(X3,sK76)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK76,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1074,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK74,X2) != sK75
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,sK75)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK75) ) )
              | ~ m1_subset_1(X3,sK74) )
          & m1_subset_1(X2,k1_zfmisc_1(sK74)) )
      & m1_subset_1(sK75,k1_zfmisc_1(sK74)) ) ),
    introduced(choice_axiom,[])).

fof(f1076,plain,
    ( k3_subset_1(sK74,sK76) != sK75
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK75)
            | ~ r2_hidden(X3,sK76) )
          & ( r2_hidden(X3,sK76)
            | r2_hidden(X3,sK75) ) )
        | ~ m1_subset_1(X3,sK74) )
    & m1_subset_1(sK76,k1_zfmisc_1(sK74))
    & m1_subset_1(sK75,k1_zfmisc_1(sK74)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK74,sK75,sK76])],[f1073,f1075,f1074])).

fof(f1833,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK76)
      | r2_hidden(X3,sK75)
      | ~ m1_subset_1(X3,sK74) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1834,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK75)
      | ~ r2_hidden(X3,sK76)
      | ~ m1_subset_1(X3,sK74) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f512,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f824,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f512])).

fof(f825,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f824])).

fof(f1069,plain,(
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
    inference(nnf_transformation,[],[f825])).

fof(f1070,plain,(
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
    inference(flattening,[],[f1069])).

fof(f1071,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( r2_hidden(sK73(X0,X1,X2),X2)
          | ~ r2_hidden(sK73(X0,X1,X2),X1) )
        & ( ~ r2_hidden(sK73(X0,X1,X2),X2)
          | r2_hidden(sK73(X0,X1,X2),X1) )
        & m1_subset_1(sK73(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1072,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( r2_hidden(sK73(X0,X1,X2),X2)
              | ~ r2_hidden(sK73(X0,X1,X2),X1) )
            & ( ~ r2_hidden(sK73(X0,X1,X2),X2)
              | r2_hidden(sK73(X0,X1,X2),X1) )
            & m1_subset_1(sK73(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK73])],[f1070,f1071])).

fof(f1830,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK73(X0,X1,X2),X2)
      | ~ r2_hidden(sK73(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1829,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK73(X0,X1,X2),X2)
      | r2_hidden(sK73(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1828,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK73(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1835,plain,(
    k3_subset_1(sK74,sK76) != sK75 ),
    inference(cnf_transformation,[],[f1076])).

fof(f1832,plain,(
    m1_subset_1(sK76,k1_zfmisc_1(sK74)) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1831,plain,(
    m1_subset_1(sK75,k1_zfmisc_1(sK74)) ),
    inference(cnf_transformation,[],[f1076])).

cnf(c_736,negated_conjecture,
    ( ~ m1_subset_1(X0,sK74)
    | r2_hidden(X0,sK75)
    | r2_hidden(X0,sK76) ),
    inference(cnf_transformation,[],[f1833])).

cnf(c_26391,plain,
    ( ~ m1_subset_1(sK73(sK74,sK75,sK76),sK74)
    | r2_hidden(sK73(sK74,sK75,sK76),sK75)
    | r2_hidden(sK73(sK74,sK75,sK76),sK76) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_26395,plain,
    ( m1_subset_1(sK73(sK74,sK75,sK76),sK74) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK75) = iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK76) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26391])).

cnf(c_735,negated_conjecture,
    ( ~ m1_subset_1(X0,sK74)
    | ~ r2_hidden(X0,sK75)
    | ~ r2_hidden(X0,sK76) ),
    inference(cnf_transformation,[],[f1834])).

cnf(c_26392,plain,
    ( ~ m1_subset_1(sK73(sK74,sK75,sK76),sK74)
    | ~ r2_hidden(sK73(sK74,sK75,sK76),sK75)
    | ~ r2_hidden(sK73(sK74,sK75,sK76),sK76) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_26393,plain,
    ( m1_subset_1(sK73(sK74,sK75,sK76),sK74) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK75) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK76) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26392])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK73(X1,X2,X0),X2)
    | r2_hidden(sK73(X1,X2,X0),X0)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1830])).

cnf(c_23557,plain,
    ( ~ m1_subset_1(sK75,k1_zfmisc_1(sK74))
    | ~ m1_subset_1(sK76,k1_zfmisc_1(sK74))
    | ~ r2_hidden(sK73(sK74,sK75,sK76),sK75)
    | r2_hidden(sK73(sK74,sK75,sK76),sK76)
    | k3_subset_1(sK74,sK76) = sK75 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_23567,plain,
    ( k3_subset_1(sK74,sK76) = sK75
    | m1_subset_1(sK75,k1_zfmisc_1(sK74)) != iProver_top
    | m1_subset_1(sK76,k1_zfmisc_1(sK74)) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK75) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK76) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23557])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK73(X1,X2,X0),X0)
    | r2_hidden(sK73(X1,X2,X0),X2)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1829])).

cnf(c_23558,plain,
    ( ~ m1_subset_1(sK75,k1_zfmisc_1(sK74))
    | ~ m1_subset_1(sK76,k1_zfmisc_1(sK74))
    | r2_hidden(sK73(sK74,sK75,sK76),sK75)
    | ~ r2_hidden(sK73(sK74,sK75,sK76),sK76)
    | k3_subset_1(sK74,sK76) = sK75 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_23565,plain,
    ( k3_subset_1(sK74,sK76) = sK75
    | m1_subset_1(sK75,k1_zfmisc_1(sK74)) != iProver_top
    | m1_subset_1(sK76,k1_zfmisc_1(sK74)) != iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK75) = iProver_top
    | r2_hidden(sK73(sK74,sK75,sK76),sK76) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23558])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK73(X1,X2,X0),X1)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1828])).

cnf(c_23560,plain,
    ( m1_subset_1(sK73(sK74,sK75,sK76),sK74)
    | ~ m1_subset_1(sK75,k1_zfmisc_1(sK74))
    | ~ m1_subset_1(sK76,k1_zfmisc_1(sK74))
    | k3_subset_1(sK74,sK76) = sK75 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_23561,plain,
    ( k3_subset_1(sK74,sK76) = sK75
    | m1_subset_1(sK73(sK74,sK75,sK76),sK74) = iProver_top
    | m1_subset_1(sK75,k1_zfmisc_1(sK74)) != iProver_top
    | m1_subset_1(sK76,k1_zfmisc_1(sK74)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23560])).

cnf(c_734,negated_conjecture,
    ( k3_subset_1(sK74,sK76) != sK75 ),
    inference(cnf_transformation,[],[f1835])).

cnf(c_737,negated_conjecture,
    ( m1_subset_1(sK76,k1_zfmisc_1(sK74)) ),
    inference(cnf_transformation,[],[f1832])).

cnf(c_746,plain,
    ( m1_subset_1(sK76,k1_zfmisc_1(sK74)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_738,negated_conjecture,
    ( m1_subset_1(sK75,k1_zfmisc_1(sK74)) ),
    inference(cnf_transformation,[],[f1831])).

cnf(c_745,plain,
    ( m1_subset_1(sK75,k1_zfmisc_1(sK74)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26395,c_26393,c_23567,c_23565,c_23561,c_734,c_746,c_745])).

%------------------------------------------------------------------------------
