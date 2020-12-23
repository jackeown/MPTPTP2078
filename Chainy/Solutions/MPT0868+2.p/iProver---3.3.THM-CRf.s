%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0868+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 31.12s
% Output     : CNFRefutation 31.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 117 expanded)
%              Number of clauses        :   28 (  34 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 370 expanded)
%              Number of equality atoms :  114 ( 272 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1308,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1307])).

fof(f2653,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1308])).

fof(f3662,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
     => ( ( k2_mcart_1(sK378) = sK378
          | k1_mcart_1(sK378) = sK378 )
        & m1_subset_1(sK378,k2_zfmisc_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3661,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK376,sK377)) )
      & k1_xboole_0 != sK377
      & k1_xboole_0 != sK376 ) ),
    introduced(choice_axiom,[])).

fof(f3663,plain,
    ( ( k2_mcart_1(sK378) = sK378
      | k1_mcart_1(sK378) = sK378 )
    & m1_subset_1(sK378,k2_zfmisc_1(sK376,sK377))
    & k1_xboole_0 != sK377
    & k1_xboole_0 != sK376 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK376,sK377,sK378])],[f2653,f3662,f3661])).

fof(f5966,plain,(
    m1_subset_1(sK378,k2_zfmisc_1(sK376,sK377)) ),
    inference(cnf_transformation,[],[f3663])).

fof(f1305,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2652,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1305])).

fof(f5962,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3683,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6691,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f5962,f3683,f3683])).

fof(f1303,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2649,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1303])).

fof(f5960,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f2649])).

fof(f6966,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f5960])).

fof(f1314,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5979,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1314])).

fof(f5959,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f2649])).

fof(f6967,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f5959])).

fof(f5978,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1314])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2583,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f2584,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2583])).

fof(f3532,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f2584])).

fof(f5801,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3532])).

fof(f1238,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2586,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1238])).

fof(f2587,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2586])).

fof(f5804,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2587])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5819,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f6673,plain,(
    ! [X0,X1] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(definition_unfolding,[],[f5819,f3683])).

fof(f5967,plain,
    ( k2_mcart_1(sK378) = sK378
    | k1_mcart_1(sK378) = sK378 ),
    inference(cnf_transformation,[],[f3663])).

fof(f5965,plain,(
    k1_xboole_0 != sK377 ),
    inference(cnf_transformation,[],[f3663])).

fof(f6693,plain,(
    o_0_0_xboole_0 != sK377 ),
    inference(definition_unfolding,[],[f5965,f3683])).

fof(f5964,plain,(
    k1_xboole_0 != sK376 ),
    inference(cnf_transformation,[],[f3663])).

fof(f6694,plain,(
    o_0_0_xboole_0 != sK376 ),
    inference(definition_unfolding,[],[f5964,f3683])).

cnf(c_2274,negated_conjecture,
    ( m1_subset_1(sK378,k2_zfmisc_1(sK376,sK377)) ),
    inference(cnf_transformation,[],[f5966])).

cnf(c_65432,plain,
    ( m1_subset_1(sK378,k2_zfmisc_1(sK376,sK377)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_2271,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f6691])).

cnf(c_65433,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_84406,plain,
    ( k4_tarski(k1_mcart_1(sK378),k2_mcart_1(sK378)) = sK378
    | sK377 = o_0_0_xboole_0
    | sK376 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_65432,c_65433])).

cnf(c_2268,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6966])).

cnf(c_2287,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5979])).

cnf(c_67556,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_2268,c_2287])).

cnf(c_96549,plain,
    ( k2_mcart_1(sK378) != sK378
    | sK377 = o_0_0_xboole_0
    | sK376 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_84406,c_67556])).

cnf(c_2269,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6967])).

cnf(c_2288,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5978])).

cnf(c_67553,plain,
    ( k4_tarski(X0,X1) != X0 ),
    inference(light_normalisation,[status(thm)],[c_2269,c_2288])).

cnf(c_95877,plain,
    ( k1_mcart_1(sK378) != sK378
    | sK377 = o_0_0_xboole_0
    | sK376 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_84406,c_67553])).

cnf(c_32458,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_87507,plain,
    ( sK376 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK376 ),
    inference(instantiation,[status(thm)],[c_32458])).

cnf(c_87508,plain,
    ( sK376 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK376
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_87507])).

cnf(c_87505,plain,
    ( sK377 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK377 ),
    inference(instantiation,[status(thm)],[c_32458])).

cnf(c_87506,plain,
    ( sK377 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK377
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_87505])).

cnf(c_2111,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f5801])).

cnf(c_2778,plain,
    ( ~ r2_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_2113,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f5804])).

cnf(c_2772,plain,
    ( r2_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_2128,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f6673])).

cnf(c_2737,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2273,negated_conjecture,
    ( k2_mcart_1(sK378) = sK378
    | k1_mcart_1(sK378) = sK378 ),
    inference(cnf_transformation,[],[f5967])).

cnf(c_2275,negated_conjecture,
    ( o_0_0_xboole_0 != sK377 ),
    inference(cnf_transformation,[],[f6693])).

cnf(c_2276,negated_conjecture,
    ( o_0_0_xboole_0 != sK376 ),
    inference(cnf_transformation,[],[f6694])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96549,c_95877,c_87508,c_87506,c_2778,c_2772,c_2737,c_2273,c_2275,c_2276])).

%------------------------------------------------------------------------------
