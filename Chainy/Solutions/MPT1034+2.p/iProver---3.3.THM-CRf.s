%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 51.62s
% Output     : CNFRefutation 51.62s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 297 expanded)
%              Number of clauses        :   41 (  75 expanded)
%              Number of leaves         :    9 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  321 (1964 expanded)
%              Number of equality atoms :  129 ( 192 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1533,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1534,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1533])).

fof(f3182,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1534])).

fof(f3183,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f3182])).

fof(f4577,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,X1,sK539)
        & r1_partfun1(X1,sK539)
        & m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK539,X0,X0)
        & v1_funct_1(sK539) ) ) ),
    introduced(choice_axiom,[])).

fof(f4576,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK537,sK537,sK538,X2)
          & r1_partfun1(sK538,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
          & v1_funct_2(X2,sK537,sK537)
          & v1_funct_1(X2) )
      & m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
      & v1_funct_2(sK538,sK537,sK537)
      & v1_funct_1(sK538) ) ),
    introduced(choice_axiom,[])).

fof(f4578,plain,
    ( ~ r2_relset_1(sK537,sK537,sK538,sK539)
    & r1_partfun1(sK538,sK539)
    & m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
    & v1_funct_2(sK539,sK537,sK537)
    & v1_funct_1(sK539)
    & m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
    & v1_funct_2(sK538,sK537,sK537)
    & v1_funct_1(sK538) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK537,sK538,sK539])],[f3183,f4577,f4576])).

fof(f7512,plain,(
    m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) ),
    inference(cnf_transformation,[],[f4578])).

fof(f1532,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3180,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1532])).

fof(f3181,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3180])).

fof(f7505,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3181])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4627,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8726,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | o_0_0_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7505,f4627])).

fof(f7510,plain,(
    v1_funct_1(sK539) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7511,plain,(
    v1_funct_2(sK539,sK537,sK537) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7507,plain,(
    v1_funct_1(sK538) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7508,plain,(
    v1_funct_2(sK538,sK537,sK537) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7513,plain,(
    r1_partfun1(sK538,sK539) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7514,plain,(
    ~ r2_relset_1(sK537,sK537,sK538,sK539) ),
    inference(cnf_transformation,[],[f4578])).

fof(f7509,plain,(
    m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) ),
    inference(cnf_transformation,[],[f4578])).

fof(f1538,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3190,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1538])).

fof(f3191,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3190])).

fof(f4583,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK542(X0,X2,X3)) != k1_funct_1(X3,sK542(X0,X2,X3))
        & r2_hidden(sK542(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4584,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK542(X0,X2,X3)) != k1_funct_1(X3,sK542(X0,X2,X3))
            & r2_hidden(sK542(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK542])],[f3191,f4583])).

fof(f7520,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK542(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4584])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3519,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f3520,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3519])).

fof(f5084,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f3520])).

fof(f7955,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f5084,f4627,f4627])).

fof(f8863,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f7955])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5154,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

cnf(c_2865,negated_conjecture,
    ( m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) ),
    inference(cnf_transformation,[],[f7512])).

cnf(c_86812,plain,
    ( m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_2862,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ r1_partfun1(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f8726])).

cnf(c_86815,plain,
    ( o_0_0_xboole_0 = X0
    | r2_relset_1(X1,X0,X2,X3) = iProver_top
    | v1_funct_2(X2,X1,X0) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | r1_partfun1(X2,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_136020,plain,
    ( sK537 = o_0_0_xboole_0
    | r2_relset_1(sK537,sK537,X0,sK539) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top
    | v1_funct_2(sK539,sK537,sK537) != iProver_top
    | r1_partfun1(X0,sK539) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK539) != iProver_top ),
    inference(superposition,[status(thm)],[c_86812,c_86815])).

cnf(c_2867,negated_conjecture,
    ( v1_funct_1(sK539) ),
    inference(cnf_transformation,[],[f7510])).

cnf(c_3027,plain,
    ( v1_funct_1(sK539) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2867])).

cnf(c_2866,negated_conjecture,
    ( v1_funct_2(sK539,sK537,sK537) ),
    inference(cnf_transformation,[],[f7511])).

cnf(c_3028,plain,
    ( v1_funct_2(sK539,sK537,sK537) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2866])).

cnf(c_137018,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | r1_partfun1(X0,sK539) != iProver_top
    | sK537 = o_0_0_xboole_0
    | r2_relset_1(sK537,sK537,X0,sK539) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_136020,c_3027,c_3028])).

cnf(c_137019,plain,
    ( sK537 = o_0_0_xboole_0
    | r2_relset_1(sK537,sK537,X0,sK539) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top
    | r1_partfun1(X0,sK539) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_137018])).

cnf(c_137035,plain,
    ( sK537 = o_0_0_xboole_0
    | r2_relset_1(sK537,sK537,sK539,sK539) = iProver_top
    | v1_funct_2(sK539,sK537,sK537) != iProver_top
    | r1_partfun1(sK539,sK539) != iProver_top
    | v1_funct_1(sK539) != iProver_top ),
    inference(superposition,[status(thm)],[c_86812,c_137019])).

cnf(c_2870,negated_conjecture,
    ( v1_funct_1(sK538) ),
    inference(cnf_transformation,[],[f7507])).

cnf(c_3024,plain,
    ( v1_funct_1(sK538) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2870])).

cnf(c_2869,negated_conjecture,
    ( v1_funct_2(sK538,sK537,sK537) ),
    inference(cnf_transformation,[],[f7508])).

cnf(c_3025,plain,
    ( v1_funct_2(sK538,sK537,sK537) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2869])).

cnf(c_2864,negated_conjecture,
    ( r1_partfun1(sK538,sK539) ),
    inference(cnf_transformation,[],[f7513])).

cnf(c_3030,plain,
    ( r1_partfun1(sK538,sK539) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2864])).

cnf(c_2863,negated_conjecture,
    ( ~ r2_relset_1(sK537,sK537,sK538,sK539) ),
    inference(cnf_transformation,[],[f7514])).

cnf(c_3031,plain,
    ( r2_relset_1(sK537,sK537,sK538,sK539) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_2868,negated_conjecture,
    ( m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) ),
    inference(cnf_transformation,[],[f7509])).

cnf(c_86809,plain,
    ( m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_137036,plain,
    ( sK537 = o_0_0_xboole_0
    | r2_relset_1(sK537,sK537,sK538,sK539) = iProver_top
    | v1_funct_2(sK538,sK537,sK537) != iProver_top
    | r1_partfun1(sK538,sK539) != iProver_top
    | v1_funct_1(sK538) != iProver_top ),
    inference(superposition,[status(thm)],[c_86809,c_137019])).

cnf(c_137115,plain,
    ( sK537 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_137035,c_3024,c_3025,c_3030,c_3031,c_137036])).

cnf(c_2877,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK542(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f7520])).

cnf(c_86800,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK542(X0,X2,X3),X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_127373,plain,
    ( r2_relset_1(sK537,sK537,sK538,X0) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top
    | v1_funct_2(sK538,sK537,sK537) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | r2_hidden(sK542(sK537,sK538,X0),sK537) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK538) != iProver_top ),
    inference(superposition,[status(thm)],[c_86809,c_86800])).

cnf(c_128295,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK542(sK537,sK538,X0),sK537) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | r2_relset_1(sK537,sK537,sK538,X0) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127373,c_3024,c_3025])).

cnf(c_128296,plain,
    ( r2_relset_1(sK537,sK537,sK538,X0) = iProver_top
    | v1_funct_2(X0,sK537,sK537) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | r2_hidden(sK542(sK537,sK538,X0),sK537) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_128295])).

cnf(c_128311,plain,
    ( r2_relset_1(sK537,sK537,sK538,sK539) = iProver_top
    | v1_funct_2(sK539,sK537,sK537) != iProver_top
    | r2_hidden(sK542(sK537,sK538,sK539),sK537) = iProver_top
    | v1_funct_1(sK539) != iProver_top ),
    inference(superposition,[status(thm)],[c_86812,c_128296])).

cnf(c_3026,plain,
    ( m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_3029,plain,
    ( m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_124359,plain,
    ( r2_relset_1(sK537,sK537,sK538,sK539)
    | ~ v1_funct_2(sK539,sK537,sK537)
    | ~ v1_funct_2(sK538,sK537,sK537)
    | ~ m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
    | ~ m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537)))
    | r2_hidden(sK542(sK537,sK538,sK539),sK537)
    | ~ v1_funct_1(sK539)
    | ~ v1_funct_1(sK538) ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_124360,plain,
    ( r2_relset_1(sK537,sK537,sK538,sK539) = iProver_top
    | v1_funct_2(sK539,sK537,sK537) != iProver_top
    | v1_funct_2(sK538,sK537,sK537) != iProver_top
    | m1_subset_1(sK539,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | m1_subset_1(sK538,k1_zfmisc_1(k2_zfmisc_1(sK537,sK537))) != iProver_top
    | r2_hidden(sK542(sK537,sK538,sK539),sK537) = iProver_top
    | v1_funct_1(sK539) != iProver_top
    | v1_funct_1(sK538) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124359])).

cnf(c_128377,plain,
    ( r2_hidden(sK542(sK537,sK538,sK539),sK537) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_128311,c_3024,c_3025,c_3026,c_3027,c_3028,c_3029,c_3031,c_124360])).

cnf(c_137137,plain,
    ( r2_hidden(sK542(o_0_0_xboole_0,sK538,sK539),o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_137115,c_128377])).

cnf(c_450,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8863])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5154])).

cnf(c_88725,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_166354,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_88725])).

cnf(c_167111,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_137137,c_166354])).

%------------------------------------------------------------------------------
