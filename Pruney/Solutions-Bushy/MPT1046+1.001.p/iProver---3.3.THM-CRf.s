%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 205 expanded)
%              Number of clauses        :   26 (  58 expanded)
%              Number of leaves         :    3 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  139 ( 807 expanded)
%              Number of equality atoms :   76 ( 293 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f13,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f4])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X2,X1] :
      ( k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) = k1_tarski(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f11])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_4,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k5_partfun1(k1_xboole_0,X1,k3_partfun1(X0,k1_xboole_0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_61,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v1_funct_1(X0)
    | k5_partfun1(k1_xboole_0,X1,k3_partfun1(X0,k1_xboole_0,X1)) = k1_tarski(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_62,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,X0)
    | ~ v1_funct_1(sK1)
    | k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_5,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_66,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,X0)
    | k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62,c_5])).

cnf(c_115,plain,
    ( k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != sK1
    | sK0 != X0
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_66])).

cnf(c_116,plain,
    ( k5_partfun1(k1_xboole_0,sK0,k3_partfun1(sK1,k1_xboole_0,sK0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_150,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k5_partfun1(k1_xboole_0,sK0,k3_partfun1(sK1,k1_xboole_0,sK0)) = k1_tarski(sK1)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)) = k1_tarski(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_82,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)) = k1_tarski(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_83,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ v1_funct_1(sK1)
    | k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_87,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_83,c_5])).

cnf(c_126,plain,
    ( k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != sK1
    | sK0 != X0
    | sK0 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_87])).

cnf(c_127,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_2,negated_conjecture,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_90,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_128,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_127,c_4,c_2,c_90])).

cnf(c_141,plain,
    ( k1_xboole_0 = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_128])).

cnf(c_149,plain,
    ( k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_141])).

cnf(c_178,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) = k1_tarski(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_150,c_149])).

cnf(c_179,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) = k1_tarski(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_178])).

cnf(c_151,negated_conjecture,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_175,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != k1_tarski(sK1) ),
    inference(light_normalisation,[status(thm)],[c_151,c_149])).

cnf(c_181,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_179,c_175])).


%------------------------------------------------------------------------------
