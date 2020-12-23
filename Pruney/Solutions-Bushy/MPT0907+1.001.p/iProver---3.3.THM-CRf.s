%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0907+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:23 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   48 (  77 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 187 expanded)
%              Number of equality atoms :   67 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( k2_mcart_1(sK0) = sK0
        | k1_mcart_1(sK0) = sK0 )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( k2_mcart_1(sK0) = sK0
      | k1_mcart_1(sK0) = sK0 )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,
    ( k2_mcart_1(sK0) = sK0
    | k1_mcart_1(sK0) = sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f14])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_134,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_155,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | k2_mcart_1(X0) != X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_85,plain,
    ( m1_subset_1(X0,X1)
    | k2_zfmisc_1(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_86,plain,
    ( m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_112,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | k2_mcart_1(X2) != X2
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_86])).

cnf(c_113,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | k2_mcart_1(sK0) != sK0 ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_5,negated_conjecture,
    ( k1_mcart_1(sK0) = sK0
    | k2_mcart_1(sK0) = sK0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | k1_mcart_1(X0) != X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_100,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | k1_mcart_1(X2) != X2
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_86])).

cnf(c_101,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | k1_mcart_1(sK0) != sK0 ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_115,plain,
    ( k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_113,c_5,c_101])).

cnf(c_116,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0,X1) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_131,plain,
    ( k2_zfmisc_1(X0_39,X0_40) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(X0_39,X0_40) = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_144,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2)
    | k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_74,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_75,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_74])).

cnf(c_92,plain,
    ( k2_zfmisc_1(sK1,sK2) != o_0_0_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_75])).

cnf(c_93,plain,
    ( k2_zfmisc_1(sK1,sK2) != o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_92])).

cnf(c_132,plain,
    ( k2_zfmisc_1(sK1,sK2) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_155,c_144,c_132])).


%------------------------------------------------------------------------------
