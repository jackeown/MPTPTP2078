%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0372+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
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
fof(f514,conjecture,(
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

fof(f515,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f514])).

fof(f829,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f515])).

fof(f830,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f829])).

fof(f1080,plain,(
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
    inference(nnf_transformation,[],[f830])).

fof(f1082,plain,(
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
     => ( k3_subset_1(X0,sK77) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,sK77)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,sK77)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK77,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1081,plain,
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
          ( k3_subset_1(sK75,X2) != sK76
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK76) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK76) ) )
              | ~ m1_subset_1(X3,sK75) )
          & m1_subset_1(X2,k1_zfmisc_1(sK75)) )
      & m1_subset_1(sK76,k1_zfmisc_1(sK75)) ) ),
    introduced(choice_axiom,[])).

fof(f1083,plain,
    ( k3_subset_1(sK75,sK77) != sK76
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK77)
            | ~ r2_hidden(X3,sK76) )
          & ( r2_hidden(X3,sK77)
            | r2_hidden(X3,sK76) ) )
        | ~ m1_subset_1(X3,sK75) )
    & m1_subset_1(sK77,k1_zfmisc_1(sK75))
    & m1_subset_1(sK76,k1_zfmisc_1(sK75)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK75,sK76,sK77])],[f1080,f1082,f1081])).

fof(f1843,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK77)
      | r2_hidden(X3,sK76)
      | ~ m1_subset_1(X3,sK75) ) ),
    inference(cnf_transformation,[],[f1083])).

fof(f1844,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK77)
      | ~ r2_hidden(X3,sK76)
      | ~ m1_subset_1(X3,sK75) ) ),
    inference(cnf_transformation,[],[f1083])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f512])).

fof(f826,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f825])).

fof(f1072,plain,(
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
    inference(nnf_transformation,[],[f826])).

fof(f1073,plain,(
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
    inference(flattening,[],[f1072])).

fof(f1074,plain,(
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

fof(f1075,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK73])],[f1073,f1074])).

fof(f1837,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK73(X0,X1,X2),X2)
      | ~ r2_hidden(sK73(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1075])).

fof(f1836,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK73(X0,X1,X2),X2)
      | r2_hidden(sK73(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1075])).

fof(f1835,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK73(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1075])).

fof(f1845,plain,(
    k3_subset_1(sK75,sK77) != sK76 ),
    inference(cnf_transformation,[],[f1083])).

fof(f1842,plain,(
    m1_subset_1(sK77,k1_zfmisc_1(sK75)) ),
    inference(cnf_transformation,[],[f1083])).

fof(f1841,plain,(
    m1_subset_1(sK76,k1_zfmisc_1(sK75)) ),
    inference(cnf_transformation,[],[f1083])).

cnf(c_739,negated_conjecture,
    ( ~ m1_subset_1(X0,sK75)
    | r2_hidden(X0,sK76)
    | r2_hidden(X0,sK77) ),
    inference(cnf_transformation,[],[f1843])).

cnf(c_26785,plain,
    ( ~ m1_subset_1(sK73(sK75,sK76,sK77),sK75)
    | r2_hidden(sK73(sK75,sK76,sK77),sK76)
    | r2_hidden(sK73(sK75,sK76,sK77),sK77) ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_26789,plain,
    ( m1_subset_1(sK73(sK75,sK76,sK77),sK75) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK76) = iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK77) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26785])).

cnf(c_738,negated_conjecture,
    ( ~ m1_subset_1(X0,sK75)
    | ~ r2_hidden(X0,sK76)
    | ~ r2_hidden(X0,sK77) ),
    inference(cnf_transformation,[],[f1844])).

cnf(c_26786,plain,
    ( ~ m1_subset_1(sK73(sK75,sK76,sK77),sK75)
    | ~ r2_hidden(sK73(sK75,sK76,sK77),sK76)
    | ~ r2_hidden(sK73(sK75,sK76,sK77),sK77) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_26787,plain,
    ( m1_subset_1(sK73(sK75,sK76,sK77),sK75) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK76) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK77) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26786])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK73(X1,X2,X0),X2)
    | r2_hidden(sK73(X1,X2,X0),X0)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1837])).

cnf(c_23669,plain,
    ( ~ m1_subset_1(sK76,k1_zfmisc_1(sK75))
    | ~ m1_subset_1(sK77,k1_zfmisc_1(sK75))
    | ~ r2_hidden(sK73(sK75,sK76,sK77),sK76)
    | r2_hidden(sK73(sK75,sK76,sK77),sK77)
    | k3_subset_1(sK75,sK77) = sK76 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_23688,plain,
    ( k3_subset_1(sK75,sK77) = sK76
    | m1_subset_1(sK76,k1_zfmisc_1(sK75)) != iProver_top
    | m1_subset_1(sK77,k1_zfmisc_1(sK75)) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK76) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK77) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23669])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK73(X1,X2,X0),X0)
    | r2_hidden(sK73(X1,X2,X0),X2)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1836])).

cnf(c_23670,plain,
    ( ~ m1_subset_1(sK76,k1_zfmisc_1(sK75))
    | ~ m1_subset_1(sK77,k1_zfmisc_1(sK75))
    | r2_hidden(sK73(sK75,sK76,sK77),sK76)
    | ~ r2_hidden(sK73(sK75,sK76,sK77),sK77)
    | k3_subset_1(sK75,sK77) = sK76 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_23686,plain,
    ( k3_subset_1(sK75,sK77) = sK76
    | m1_subset_1(sK76,k1_zfmisc_1(sK75)) != iProver_top
    | m1_subset_1(sK77,k1_zfmisc_1(sK75)) != iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK76) = iProver_top
    | r2_hidden(sK73(sK75,sK76,sK77),sK77) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23670])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK73(X1,X2,X0),X1)
    | k3_subset_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f1835])).

cnf(c_23674,plain,
    ( m1_subset_1(sK73(sK75,sK76,sK77),sK75)
    | ~ m1_subset_1(sK76,k1_zfmisc_1(sK75))
    | ~ m1_subset_1(sK77,k1_zfmisc_1(sK75))
    | k3_subset_1(sK75,sK77) = sK76 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_23678,plain,
    ( k3_subset_1(sK75,sK77) = sK76
    | m1_subset_1(sK73(sK75,sK76,sK77),sK75) = iProver_top
    | m1_subset_1(sK76,k1_zfmisc_1(sK75)) != iProver_top
    | m1_subset_1(sK77,k1_zfmisc_1(sK75)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23674])).

cnf(c_737,negated_conjecture,
    ( k3_subset_1(sK75,sK77) != sK76 ),
    inference(cnf_transformation,[],[f1845])).

cnf(c_740,negated_conjecture,
    ( m1_subset_1(sK77,k1_zfmisc_1(sK75)) ),
    inference(cnf_transformation,[],[f1842])).

cnf(c_749,plain,
    ( m1_subset_1(sK77,k1_zfmisc_1(sK75)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_741,negated_conjecture,
    ( m1_subset_1(sK76,k1_zfmisc_1(sK75)) ),
    inference(cnf_transformation,[],[f1841])).

cnf(c_748,plain,
    ( m1_subset_1(sK76,k1_zfmisc_1(sK75)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26789,c_26787,c_23688,c_23686,c_23678,c_737,c_749,c_748])).

%------------------------------------------------------------------------------
