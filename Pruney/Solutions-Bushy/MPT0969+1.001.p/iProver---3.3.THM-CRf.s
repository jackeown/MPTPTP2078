%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0969+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:31 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 212 expanded)
%              Number of clauses        :   30 (  65 expanded)
%              Number of leaves         :    3 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 ( 830 expanded)
%              Number of equality atoms :   53 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0))
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
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f4])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f11])).

fof(f15,plain,(
    ~ r2_hidden(sK1,k1_funct_2(sK0,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_4,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(sK1,k1_funct_2(sK0,sK0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_68,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_funct_2(k1_xboole_0,X1) != k1_funct_2(sK0,sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_69,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK1)
    | k1_funct_2(k1_xboole_0,X0) != k1_funct_2(sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_68])).

cnf(c_5,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_73,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,X0)
    | k1_funct_2(k1_xboole_0,X0) != k1_funct_2(sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_69,c_5])).

cnf(c_74,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_funct_2(k1_xboole_0,X0) != k1_funct_2(sK0,sK0) ),
    inference(renaming,[status(thm)],[c_73])).

cnf(c_168,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_funct_2(k1_xboole_0,X0) != k1_funct_2(sK0,sK0)
    | sK0 != X0
    | sK0 != k1_xboole_0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_74])).

cnf(c_169,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_funct_2(k1_xboole_0,sK0) != k1_funct_2(sK0,sK0)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_253,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_funct_2(k1_xboole_0,sK0) != k1_funct_2(sK0,sK0)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_317,plain,
    ( k1_funct_2(k1_xboole_0,sK0) != k1_funct_2(sK0,sK0)
    | sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_89,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_funct_2(X1,X2) != k1_funct_2(sK0,sK0)
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_90,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k1_funct_2(X0,X1) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_94,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK1,X0,X1)
    | k1_funct_2(X0,X1) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_90,c_5])).

cnf(c_95,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_2(X0,X1) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_94])).

cnf(c_181,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_2(X0,X1) != k1_funct_2(sK0,sK0)
    | sK0 != X0
    | sK0 != X1
    | sK1 != sK1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_95])).

cnf(c_182,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_2(sK0,sK0) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_97,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_2(sK0,sK0) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_184,plain,
    ( k1_funct_2(sK0,sK0) != k1_funct_2(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_4,c_3,c_97])).

cnf(c_217,plain,
    ( k1_xboole_0 = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_184])).

cnf(c_252,plain,
    ( k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_217])).

cnf(c_323,plain,
    ( k1_funct_2(k1_xboole_0,k1_xboole_0) != k1_funct_2(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_317,c_252])).

cnf(c_324,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_323])).

cnf(c_254,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_316,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_320,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_316,c_252])).

cnf(c_326,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_324,c_320])).


%------------------------------------------------------------------------------
