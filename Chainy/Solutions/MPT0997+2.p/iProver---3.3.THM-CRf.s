%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0997+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 41.99s
% Output     : CNFRefutation 41.99s
% Verified   : 
% Statistics : Number of formulae       :   48 (  77 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 235 expanded)
%              Number of equality atoms :  117 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1258,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2833,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1258])).

fof(f6552,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2833])).

fof(f1342,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2892,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1342])).

fof(f6741,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2892])).

fof(f1280,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6602,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1280])).

fof(f8102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6741,f6602,f6602])).

fof(f1371,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4194,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1371])).

fof(f4195,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f4194])).

fof(f6798,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f4195])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4401,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1283,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6605,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1283])).

fof(f1281,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6603,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1281])).

fof(f7300,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6605,f6603])).

fof(f8163,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f6798,f4401,f4401,f7300])).

fof(f8666,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f8163])).

fof(f6797,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4195])).

fof(f8164,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6797,f4401,f7300,f4401,f4401,f4401,f4401])).

fof(f1522,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1523,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f1522])).

fof(f3108,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1523])).

fof(f3109,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3108])).

fof(f4390,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK538,sK539,sK540) != k7_relset_1(sK538,sK539,sK540,sK538)
      & ( k1_xboole_0 = sK538
        | k1_xboole_0 != sK539 )
      & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
      & v1_funct_2(sK540,sK538,sK539)
      & v1_funct_1(sK540) ) ),
    introduced(choice_axiom,[])).

fof(f4391,plain,
    ( k2_relset_1(sK538,sK539,sK540) != k7_relset_1(sK538,sK539,sK540,sK538)
    & ( k1_xboole_0 = sK538
      | k1_xboole_0 != sK539 )
    & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
    & v1_funct_2(sK540,sK538,sK539)
    & v1_funct_1(sK540) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK538,sK539,sK540])],[f3109,f4390])).

fof(f7266,plain,(
    k2_relset_1(sK538,sK539,sK540) != k7_relset_1(sK538,sK539,sK540,sK538) ),
    inference(cnf_transformation,[],[f4391])).

fof(f7264,plain,(
    m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f4391])).

cnf(c_40852,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_134267,plain,
    ( k7_relset_1(sK538,sK539,sK540,sK538) != k2_relset_1(sK538,sK539,sK540)
    | k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k4_tarski(k4_tarski(X0,X1),k7_relset_1(sK538,sK539,sK540,sK538)) = k4_tarski(k4_tarski(X2,X3),k2_relset_1(sK538,sK539,sK540)) ),
    inference(instantiation,[status(thm)],[c_40852])).

cnf(c_134268,plain,
    ( k7_relset_1(sK538,sK539,sK540,sK538) != k2_relset_1(sK538,sK539,sK540)
    | k4_tarski(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),k7_relset_1(sK538,sK539,sK540,sK538)) = k4_tarski(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),k2_relset_1(sK538,sK539,sK540))
    | k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_134267])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f6552])).

cnf(c_133621,plain,
    ( ~ m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
    | k7_relset_1(sK538,sK539,sK540,sK538) = k2_relset_1(sK538,sK539,sK540) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_2322,plain,
    ( X0 = X1
    | k4_tarski(k4_tarski(X2,X3),X1) != k4_tarski(k4_tarski(X4,X5),X0) ),
    inference(cnf_transformation,[],[f8102])).

cnf(c_115367,plain,
    ( k2_relset_1(sK538,sK539,sK540) = k7_relset_1(sK538,sK539,sK540,sK538)
    | k4_tarski(k4_tarski(X0,X1),k7_relset_1(sK538,sK539,sK540,sK538)) != k4_tarski(k4_tarski(X2,X3),k2_relset_1(sK538,sK539,sK540)) ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_115368,plain,
    ( k2_relset_1(sK538,sK539,sK540) = k7_relset_1(sK538,sK539,sK540,sK538)
    | k4_tarski(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),k7_relset_1(sK538,sK539,sK540,sK538)) != k4_tarski(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),k2_relset_1(sK538,sK539,sK540)) ),
    inference(instantiation,[status(thm)],[c_115367])).

cnf(c_40986,plain,
    ( k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_40852])).

cnf(c_2383,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0),X1),X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8666])).

cnf(c_4174,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_2384,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f8164])).

cnf(c_4173,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2844,negated_conjecture,
    ( k2_relset_1(sK538,sK539,sK540) != k7_relset_1(sK538,sK539,sK540,sK538) ),
    inference(cnf_transformation,[],[f7266])).

cnf(c_2846,negated_conjecture,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f7264])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134268,c_133621,c_115368,c_40986,c_4174,c_4173,c_2844,c_2846])).

%------------------------------------------------------------------------------
