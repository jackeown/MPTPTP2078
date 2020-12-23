%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 39.66s
% Output     : CNFRefutation 39.66s
% Verified   : 
% Statistics : Number of formulae       :   29 (  49 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 133 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1528,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3133,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1528])).

fof(f3134,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f3133])).

fof(f7316,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f3134])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1633,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f4585,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1633])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4446,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7457,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f4585,f4446,f4446])).

fof(f1537,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1538,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f1537])).

fof(f3151,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1538])).

fof(f3152,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3151])).

fof(f4437,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK540,sK542,sK541)
      & m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK540)))
      & v1_funct_2(sK542,k1_xboole_0,sK540)
      & v1_funct_1(sK542) ) ),
    introduced(choice_axiom,[])).

fof(f4438,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK540,sK542,sK541)
    & m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK540)))
    & v1_funct_2(sK542,k1_xboole_0,sK540)
    & v1_funct_1(sK542) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK540,sK541,sK542])],[f3152,f4437])).

fof(f7341,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK540,sK542,sK541) ),
    inference(cnf_transformation,[],[f4438])).

fof(f8451,plain,(
    o_0_0_xboole_0 != k8_relset_1(o_0_0_xboole_0,sK540,sK542,sK541) ),
    inference(definition_unfolding,[],[f7341,f4446,f4446])).

fof(f7340,plain,(
    m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK540))) ),
    inference(cnf_transformation,[],[f4438])).

fof(f8452,plain,(
    m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK540))) ),
    inference(definition_unfolding,[],[f7340,f4446])).

fof(f7338,plain,(
    v1_funct_1(sK542) ),
    inference(cnf_transformation,[],[f4438])).

cnf(c_2853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f7316])).

cnf(c_130261,plain,
    ( ~ m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK540)))
    | r1_tarski(k8_relset_1(o_0_0_xboole_0,sK540,sK542,sK541),o_0_0_xboole_0)
    | ~ v1_funct_1(sK542) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f7457])).

cnf(c_107768,plain,
    ( ~ r1_tarski(k8_relset_1(o_0_0_xboole_0,sK540,sK542,sK541),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k8_relset_1(o_0_0_xboole_0,sK540,sK542,sK541) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_2875,negated_conjecture,
    ( o_0_0_xboole_0 != k8_relset_1(o_0_0_xboole_0,sK540,sK542,sK541) ),
    inference(cnf_transformation,[],[f8451])).

cnf(c_2876,negated_conjecture,
    ( m1_subset_1(sK542,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK540))) ),
    inference(cnf_transformation,[],[f8452])).

cnf(c_2878,negated_conjecture,
    ( v1_funct_1(sK542) ),
    inference(cnf_transformation,[],[f7338])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130261,c_107768,c_2875,c_2876,c_2878])).

%------------------------------------------------------------------------------
