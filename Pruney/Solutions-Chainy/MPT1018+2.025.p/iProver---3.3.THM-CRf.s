%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:03 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 552 expanded)
%              Number of clauses        :   58 ( 168 expanded)
%              Number of leaves         :   10 ( 146 expanded)
%              Depth                    :   22
%              Number of atoms          :  270 (3483 expanded)
%              Number of equality atoms :  111 (1091 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK2 != sK3
        & k1_funct_1(X1,sK2) = k1_funct_1(X1,sK3)
        & r2_hidden(sK3,X0)
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).

fof(f31,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_149,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_150,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_154,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK1,X0,X1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_150,c_13])).

cnf(c_155,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
    | sK0 != X1
    | sK0 != X2
    | sK1 != sK1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_155])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_206,plain,
    ( ~ r2_hidden(X0,sK0)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_202,c_11])).

cnf(c_252,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
    | sK0 != sK0
    | sK0 = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_206])).

cnf(c_253,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_301,plain,
    ( sK0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_253])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_244,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
    | sK0 != sK0
    | sK0 = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_206])).

cnf(c_245,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_302,plain,
    ( sK0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3 ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_7,negated_conjecture,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_306,negated_conjecture,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_421,plain,
    ( sK0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_302,c_306])).

cnf(c_499,plain,
    ( sK0 = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_301,c_421])).

cnf(c_311,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_329,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_6,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_307,negated_conjecture,
    ( sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_314,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_449,plain,
    ( sK3 != X0_45
    | sK2 != X0_45
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_450,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_559,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_329,c_307,c_450])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_182,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_183,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k1_relset_1(X0,X0,sK1) = X0 ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_222,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k1_relset_1(X0,X0,sK1) = X0
    | sK0 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_183])).

cnf(c_223,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_185,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_225,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_12,c_11,c_185])).

cnf(c_304,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_564,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_559,c_304])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_407,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_746,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_564,c_407])).

cnf(c_305,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_409,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_563,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_559,c_409])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_134,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_135,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_134])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | sK0 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_8])).

cnf(c_236,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_303,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subtyping,[status(esa)],[c_236])).

cnf(c_410,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_562,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_559,c_410])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_746,c_563,c_562])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.09/0.99  
% 1.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.09/0.99  
% 1.09/0.99  ------  iProver source info
% 1.09/0.99  
% 1.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.09/0.99  git: non_committed_changes: false
% 1.09/0.99  git: last_make_outside_of_git: false
% 1.09/0.99  
% 1.09/0.99  ------ 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options
% 1.09/0.99  
% 1.09/0.99  --out_options                           all
% 1.09/0.99  --tptp_safe_out                         true
% 1.09/0.99  --problem_path                          ""
% 1.09/0.99  --include_path                          ""
% 1.09/0.99  --clausifier                            res/vclausify_rel
% 1.09/0.99  --clausifier_options                    --mode clausify
% 1.09/0.99  --stdin                                 false
% 1.09/0.99  --stats_out                             all
% 1.09/0.99  
% 1.09/0.99  ------ General Options
% 1.09/0.99  
% 1.09/0.99  --fof                                   false
% 1.09/0.99  --time_out_real                         305.
% 1.09/0.99  --time_out_virtual                      -1.
% 1.09/0.99  --symbol_type_check                     false
% 1.09/0.99  --clausify_out                          false
% 1.09/0.99  --sig_cnt_out                           false
% 1.09/0.99  --trig_cnt_out                          false
% 1.09/0.99  --trig_cnt_out_tolerance                1.
% 1.09/0.99  --trig_cnt_out_sk_spl                   false
% 1.09/0.99  --abstr_cl_out                          false
% 1.09/0.99  
% 1.09/0.99  ------ Global Options
% 1.09/0.99  
% 1.09/0.99  --schedule                              default
% 1.09/0.99  --add_important_lit                     false
% 1.09/0.99  --prop_solver_per_cl                    1000
% 1.09/0.99  --min_unsat_core                        false
% 1.09/0.99  --soft_assumptions                      false
% 1.09/0.99  --soft_lemma_size                       3
% 1.09/0.99  --prop_impl_unit_size                   0
% 1.09/0.99  --prop_impl_unit                        []
% 1.09/0.99  --share_sel_clauses                     true
% 1.09/0.99  --reset_solvers                         false
% 1.09/0.99  --bc_imp_inh                            [conj_cone]
% 1.09/0.99  --conj_cone_tolerance                   3.
% 1.09/0.99  --extra_neg_conj                        none
% 1.09/0.99  --large_theory_mode                     true
% 1.09/0.99  --prolific_symb_bound                   200
% 1.09/0.99  --lt_threshold                          2000
% 1.09/0.99  --clause_weak_htbl                      true
% 1.09/0.99  --gc_record_bc_elim                     false
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing Options
% 1.09/0.99  
% 1.09/0.99  --preprocessing_flag                    true
% 1.09/0.99  --time_out_prep_mult                    0.1
% 1.09/0.99  --splitting_mode                        input
% 1.09/0.99  --splitting_grd                         true
% 1.09/0.99  --splitting_cvd                         false
% 1.09/0.99  --splitting_cvd_svl                     false
% 1.09/0.99  --splitting_nvd                         32
% 1.09/0.99  --sub_typing                            true
% 1.09/0.99  --prep_gs_sim                           true
% 1.09/0.99  --prep_unflatten                        true
% 1.09/0.99  --prep_res_sim                          true
% 1.09/0.99  --prep_upred                            true
% 1.09/0.99  --prep_sem_filter                       exhaustive
% 1.09/0.99  --prep_sem_filter_out                   false
% 1.09/0.99  --pred_elim                             true
% 1.09/0.99  --res_sim_input                         true
% 1.09/0.99  --eq_ax_congr_red                       true
% 1.09/0.99  --pure_diseq_elim                       true
% 1.09/0.99  --brand_transform                       false
% 1.09/0.99  --non_eq_to_eq                          false
% 1.09/0.99  --prep_def_merge                        true
% 1.09/0.99  --prep_def_merge_prop_impl              false
% 1.09/0.99  --prep_def_merge_mbd                    true
% 1.09/0.99  --prep_def_merge_tr_red                 false
% 1.09/0.99  --prep_def_merge_tr_cl                  false
% 1.09/0.99  --smt_preprocessing                     true
% 1.09/0.99  --smt_ac_axioms                         fast
% 1.09/0.99  --preprocessed_out                      false
% 1.09/0.99  --preprocessed_stats                    false
% 1.09/0.99  
% 1.09/0.99  ------ Abstraction refinement Options
% 1.09/0.99  
% 1.09/0.99  --abstr_ref                             []
% 1.09/0.99  --abstr_ref_prep                        false
% 1.09/0.99  --abstr_ref_until_sat                   false
% 1.09/0.99  --abstr_ref_sig_restrict                funpre
% 1.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/0.99  --abstr_ref_under                       []
% 1.09/0.99  
% 1.09/0.99  ------ SAT Options
% 1.09/0.99  
% 1.09/0.99  --sat_mode                              false
% 1.09/0.99  --sat_fm_restart_options                ""
% 1.09/0.99  --sat_gr_def                            false
% 1.09/0.99  --sat_epr_types                         true
% 1.09/0.99  --sat_non_cyclic_types                  false
% 1.09/0.99  --sat_finite_models                     false
% 1.09/0.99  --sat_fm_lemmas                         false
% 1.09/0.99  --sat_fm_prep                           false
% 1.09/0.99  --sat_fm_uc_incr                        true
% 1.09/0.99  --sat_out_model                         small
% 1.09/0.99  --sat_out_clauses                       false
% 1.09/0.99  
% 1.09/0.99  ------ QBF Options
% 1.09/0.99  
% 1.09/0.99  --qbf_mode                              false
% 1.09/0.99  --qbf_elim_univ                         false
% 1.09/0.99  --qbf_dom_inst                          none
% 1.09/0.99  --qbf_dom_pre_inst                      false
% 1.09/0.99  --qbf_sk_in                             false
% 1.09/0.99  --qbf_pred_elim                         true
% 1.09/0.99  --qbf_split                             512
% 1.09/0.99  
% 1.09/0.99  ------ BMC1 Options
% 1.09/0.99  
% 1.09/0.99  --bmc1_incremental                      false
% 1.09/0.99  --bmc1_axioms                           reachable_all
% 1.09/0.99  --bmc1_min_bound                        0
% 1.09/0.99  --bmc1_max_bound                        -1
% 1.09/0.99  --bmc1_max_bound_default                -1
% 1.09/0.99  --bmc1_symbol_reachability              true
% 1.09/0.99  --bmc1_property_lemmas                  false
% 1.09/0.99  --bmc1_k_induction                      false
% 1.09/0.99  --bmc1_non_equiv_states                 false
% 1.09/0.99  --bmc1_deadlock                         false
% 1.09/0.99  --bmc1_ucm                              false
% 1.09/0.99  --bmc1_add_unsat_core                   none
% 1.09/0.99  --bmc1_unsat_core_children              false
% 1.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/0.99  --bmc1_out_stat                         full
% 1.09/0.99  --bmc1_ground_init                      false
% 1.09/0.99  --bmc1_pre_inst_next_state              false
% 1.09/0.99  --bmc1_pre_inst_state                   false
% 1.09/0.99  --bmc1_pre_inst_reach_state             false
% 1.09/0.99  --bmc1_out_unsat_core                   false
% 1.09/0.99  --bmc1_aig_witness_out                  false
% 1.09/0.99  --bmc1_verbose                          false
% 1.09/0.99  --bmc1_dump_clauses_tptp                false
% 1.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.09/0.99  --bmc1_dump_file                        -
% 1.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.09/0.99  --bmc1_ucm_extend_mode                  1
% 1.09/0.99  --bmc1_ucm_init_mode                    2
% 1.09/0.99  --bmc1_ucm_cone_mode                    none
% 1.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.09/0.99  --bmc1_ucm_relax_model                  4
% 1.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/0.99  --bmc1_ucm_layered_model                none
% 1.09/0.99  --bmc1_ucm_max_lemma_size               10
% 1.09/0.99  
% 1.09/0.99  ------ AIG Options
% 1.09/0.99  
% 1.09/0.99  --aig_mode                              false
% 1.09/0.99  
% 1.09/0.99  ------ Instantiation Options
% 1.09/0.99  
% 1.09/0.99  --instantiation_flag                    true
% 1.09/0.99  --inst_sos_flag                         false
% 1.09/0.99  --inst_sos_phase                        true
% 1.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel_side                     num_symb
% 1.09/0.99  --inst_solver_per_active                1400
% 1.09/0.99  --inst_solver_calls_frac                1.
% 1.09/0.99  --inst_passive_queue_type               priority_queues
% 1.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/0.99  --inst_passive_queues_freq              [25;2]
% 1.09/0.99  --inst_dismatching                      true
% 1.09/0.99  --inst_eager_unprocessed_to_passive     true
% 1.09/0.99  --inst_prop_sim_given                   true
% 1.09/0.99  --inst_prop_sim_new                     false
% 1.09/0.99  --inst_subs_new                         false
% 1.09/0.99  --inst_eq_res_simp                      false
% 1.09/0.99  --inst_subs_given                       false
% 1.09/0.99  --inst_orphan_elimination               true
% 1.09/0.99  --inst_learning_loop_flag               true
% 1.09/0.99  --inst_learning_start                   3000
% 1.09/0.99  --inst_learning_factor                  2
% 1.09/0.99  --inst_start_prop_sim_after_learn       3
% 1.09/0.99  --inst_sel_renew                        solver
% 1.09/0.99  --inst_lit_activity_flag                true
% 1.09/0.99  --inst_restr_to_given                   false
% 1.09/0.99  --inst_activity_threshold               500
% 1.09/0.99  --inst_out_proof                        true
% 1.09/0.99  
% 1.09/0.99  ------ Resolution Options
% 1.09/0.99  
% 1.09/0.99  --resolution_flag                       true
% 1.09/0.99  --res_lit_sel                           adaptive
% 1.09/0.99  --res_lit_sel_side                      none
% 1.09/0.99  --res_ordering                          kbo
% 1.09/0.99  --res_to_prop_solver                    active
% 1.09/0.99  --res_prop_simpl_new                    false
% 1.09/0.99  --res_prop_simpl_given                  true
% 1.09/0.99  --res_passive_queue_type                priority_queues
% 1.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/0.99  --res_passive_queues_freq               [15;5]
% 1.09/0.99  --res_forward_subs                      full
% 1.09/0.99  --res_backward_subs                     full
% 1.09/0.99  --res_forward_subs_resolution           true
% 1.09/0.99  --res_backward_subs_resolution          true
% 1.09/0.99  --res_orphan_elimination                true
% 1.09/0.99  --res_time_limit                        2.
% 1.09/0.99  --res_out_proof                         true
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Options
% 1.09/0.99  
% 1.09/0.99  --superposition_flag                    true
% 1.09/0.99  --sup_passive_queue_type                priority_queues
% 1.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.09/0.99  --demod_completeness_check              fast
% 1.09/0.99  --demod_use_ground                      true
% 1.09/0.99  --sup_to_prop_solver                    passive
% 1.09/0.99  --sup_prop_simpl_new                    true
% 1.09/0.99  --sup_prop_simpl_given                  true
% 1.09/0.99  --sup_fun_splitting                     false
% 1.09/0.99  --sup_smt_interval                      50000
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Simplification Setup
% 1.09/0.99  
% 1.09/0.99  --sup_indices_passive                   []
% 1.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_full_bw                           [BwDemod]
% 1.09/0.99  --sup_immed_triv                        [TrivRules]
% 1.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_immed_bw_main                     []
% 1.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  
% 1.09/0.99  ------ Combination Options
% 1.09/0.99  
% 1.09/0.99  --comb_res_mult                         3
% 1.09/0.99  --comb_sup_mult                         2
% 1.09/0.99  --comb_inst_mult                        10
% 1.09/0.99  
% 1.09/0.99  ------ Debug Options
% 1.09/0.99  
% 1.09/0.99  --dbg_backtrace                         false
% 1.09/0.99  --dbg_dump_prop_clauses                 false
% 1.09/0.99  --dbg_dump_prop_clauses_file            -
% 1.09/0.99  --dbg_out_stat                          false
% 1.09/0.99  ------ Parsing...
% 1.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.09/0.99  ------ Proving...
% 1.09/0.99  ------ Problem Properties 
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  clauses                                 9
% 1.09/0.99  conjectures                             3
% 1.09/0.99  EPR                                     1
% 1.09/0.99  Horn                                    7
% 1.09/0.99  unary                                   5
% 1.09/0.99  binary                                  4
% 1.09/0.99  lits                                    13
% 1.09/0.99  lits eq                                 8
% 1.09/0.99  fd_pure                                 0
% 1.09/0.99  fd_pseudo                               0
% 1.09/0.99  fd_cond                                 0
% 1.09/0.99  fd_pseudo_cond                          0
% 1.09/0.99  AC symbols                              0
% 1.09/0.99  
% 1.09/0.99  ------ Schedule dynamic 5 is on 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  ------ 
% 1.09/0.99  Current options:
% 1.09/0.99  ------ 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options
% 1.09/0.99  
% 1.09/0.99  --out_options                           all
% 1.09/0.99  --tptp_safe_out                         true
% 1.09/0.99  --problem_path                          ""
% 1.09/0.99  --include_path                          ""
% 1.09/0.99  --clausifier                            res/vclausify_rel
% 1.09/0.99  --clausifier_options                    --mode clausify
% 1.09/0.99  --stdin                                 false
% 1.09/0.99  --stats_out                             all
% 1.09/0.99  
% 1.09/0.99  ------ General Options
% 1.09/0.99  
% 1.09/0.99  --fof                                   false
% 1.09/0.99  --time_out_real                         305.
% 1.09/0.99  --time_out_virtual                      -1.
% 1.09/0.99  --symbol_type_check                     false
% 1.09/0.99  --clausify_out                          false
% 1.09/0.99  --sig_cnt_out                           false
% 1.09/0.99  --trig_cnt_out                          false
% 1.09/0.99  --trig_cnt_out_tolerance                1.
% 1.09/0.99  --trig_cnt_out_sk_spl                   false
% 1.09/0.99  --abstr_cl_out                          false
% 1.09/0.99  
% 1.09/0.99  ------ Global Options
% 1.09/0.99  
% 1.09/0.99  --schedule                              default
% 1.09/0.99  --add_important_lit                     false
% 1.09/0.99  --prop_solver_per_cl                    1000
% 1.09/0.99  --min_unsat_core                        false
% 1.09/0.99  --soft_assumptions                      false
% 1.09/0.99  --soft_lemma_size                       3
% 1.09/0.99  --prop_impl_unit_size                   0
% 1.09/0.99  --prop_impl_unit                        []
% 1.09/0.99  --share_sel_clauses                     true
% 1.09/0.99  --reset_solvers                         false
% 1.09/0.99  --bc_imp_inh                            [conj_cone]
% 1.09/0.99  --conj_cone_tolerance                   3.
% 1.09/0.99  --extra_neg_conj                        none
% 1.09/0.99  --large_theory_mode                     true
% 1.09/0.99  --prolific_symb_bound                   200
% 1.09/0.99  --lt_threshold                          2000
% 1.09/0.99  --clause_weak_htbl                      true
% 1.09/0.99  --gc_record_bc_elim                     false
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing Options
% 1.09/0.99  
% 1.09/0.99  --preprocessing_flag                    true
% 1.09/0.99  --time_out_prep_mult                    0.1
% 1.09/0.99  --splitting_mode                        input
% 1.09/0.99  --splitting_grd                         true
% 1.09/0.99  --splitting_cvd                         false
% 1.09/0.99  --splitting_cvd_svl                     false
% 1.09/0.99  --splitting_nvd                         32
% 1.09/0.99  --sub_typing                            true
% 1.09/0.99  --prep_gs_sim                           true
% 1.09/0.99  --prep_unflatten                        true
% 1.09/0.99  --prep_res_sim                          true
% 1.09/0.99  --prep_upred                            true
% 1.09/0.99  --prep_sem_filter                       exhaustive
% 1.09/0.99  --prep_sem_filter_out                   false
% 1.09/0.99  --pred_elim                             true
% 1.09/0.99  --res_sim_input                         true
% 1.09/0.99  --eq_ax_congr_red                       true
% 1.09/0.99  --pure_diseq_elim                       true
% 1.09/0.99  --brand_transform                       false
% 1.09/0.99  --non_eq_to_eq                          false
% 1.09/0.99  --prep_def_merge                        true
% 1.09/0.99  --prep_def_merge_prop_impl              false
% 1.09/0.99  --prep_def_merge_mbd                    true
% 1.09/0.99  --prep_def_merge_tr_red                 false
% 1.09/0.99  --prep_def_merge_tr_cl                  false
% 1.09/0.99  --smt_preprocessing                     true
% 1.09/0.99  --smt_ac_axioms                         fast
% 1.09/0.99  --preprocessed_out                      false
% 1.09/0.99  --preprocessed_stats                    false
% 1.09/0.99  
% 1.09/0.99  ------ Abstraction refinement Options
% 1.09/0.99  
% 1.09/0.99  --abstr_ref                             []
% 1.09/0.99  --abstr_ref_prep                        false
% 1.09/0.99  --abstr_ref_until_sat                   false
% 1.09/0.99  --abstr_ref_sig_restrict                funpre
% 1.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/0.99  --abstr_ref_under                       []
% 1.09/0.99  
% 1.09/0.99  ------ SAT Options
% 1.09/0.99  
% 1.09/0.99  --sat_mode                              false
% 1.09/0.99  --sat_fm_restart_options                ""
% 1.09/0.99  --sat_gr_def                            false
% 1.09/0.99  --sat_epr_types                         true
% 1.09/0.99  --sat_non_cyclic_types                  false
% 1.09/0.99  --sat_finite_models                     false
% 1.09/0.99  --sat_fm_lemmas                         false
% 1.09/0.99  --sat_fm_prep                           false
% 1.09/0.99  --sat_fm_uc_incr                        true
% 1.09/0.99  --sat_out_model                         small
% 1.09/0.99  --sat_out_clauses                       false
% 1.09/0.99  
% 1.09/0.99  ------ QBF Options
% 1.09/0.99  
% 1.09/0.99  --qbf_mode                              false
% 1.09/0.99  --qbf_elim_univ                         false
% 1.09/0.99  --qbf_dom_inst                          none
% 1.09/0.99  --qbf_dom_pre_inst                      false
% 1.09/0.99  --qbf_sk_in                             false
% 1.09/0.99  --qbf_pred_elim                         true
% 1.09/0.99  --qbf_split                             512
% 1.09/0.99  
% 1.09/0.99  ------ BMC1 Options
% 1.09/0.99  
% 1.09/0.99  --bmc1_incremental                      false
% 1.09/0.99  --bmc1_axioms                           reachable_all
% 1.09/0.99  --bmc1_min_bound                        0
% 1.09/0.99  --bmc1_max_bound                        -1
% 1.09/0.99  --bmc1_max_bound_default                -1
% 1.09/0.99  --bmc1_symbol_reachability              true
% 1.09/0.99  --bmc1_property_lemmas                  false
% 1.09/0.99  --bmc1_k_induction                      false
% 1.09/0.99  --bmc1_non_equiv_states                 false
% 1.09/0.99  --bmc1_deadlock                         false
% 1.09/0.99  --bmc1_ucm                              false
% 1.09/0.99  --bmc1_add_unsat_core                   none
% 1.09/0.99  --bmc1_unsat_core_children              false
% 1.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/0.99  --bmc1_out_stat                         full
% 1.09/0.99  --bmc1_ground_init                      false
% 1.09/0.99  --bmc1_pre_inst_next_state              false
% 1.09/0.99  --bmc1_pre_inst_state                   false
% 1.09/0.99  --bmc1_pre_inst_reach_state             false
% 1.09/0.99  --bmc1_out_unsat_core                   false
% 1.09/0.99  --bmc1_aig_witness_out                  false
% 1.09/0.99  --bmc1_verbose                          false
% 1.09/0.99  --bmc1_dump_clauses_tptp                false
% 1.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.09/0.99  --bmc1_dump_file                        -
% 1.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.09/0.99  --bmc1_ucm_extend_mode                  1
% 1.09/0.99  --bmc1_ucm_init_mode                    2
% 1.09/0.99  --bmc1_ucm_cone_mode                    none
% 1.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.09/0.99  --bmc1_ucm_relax_model                  4
% 1.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/0.99  --bmc1_ucm_layered_model                none
% 1.09/0.99  --bmc1_ucm_max_lemma_size               10
% 1.09/0.99  
% 1.09/0.99  ------ AIG Options
% 1.09/0.99  
% 1.09/0.99  --aig_mode                              false
% 1.09/0.99  
% 1.09/0.99  ------ Instantiation Options
% 1.09/0.99  
% 1.09/0.99  --instantiation_flag                    true
% 1.09/0.99  --inst_sos_flag                         false
% 1.09/0.99  --inst_sos_phase                        true
% 1.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel_side                     none
% 1.09/0.99  --inst_solver_per_active                1400
% 1.09/0.99  --inst_solver_calls_frac                1.
% 1.09/0.99  --inst_passive_queue_type               priority_queues
% 1.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/0.99  --inst_passive_queues_freq              [25;2]
% 1.09/0.99  --inst_dismatching                      true
% 1.09/0.99  --inst_eager_unprocessed_to_passive     true
% 1.09/0.99  --inst_prop_sim_given                   true
% 1.09/0.99  --inst_prop_sim_new                     false
% 1.09/0.99  --inst_subs_new                         false
% 1.09/0.99  --inst_eq_res_simp                      false
% 1.09/0.99  --inst_subs_given                       false
% 1.09/0.99  --inst_orphan_elimination               true
% 1.09/0.99  --inst_learning_loop_flag               true
% 1.09/0.99  --inst_learning_start                   3000
% 1.09/0.99  --inst_learning_factor                  2
% 1.09/0.99  --inst_start_prop_sim_after_learn       3
% 1.09/0.99  --inst_sel_renew                        solver
% 1.09/0.99  --inst_lit_activity_flag                true
% 1.09/0.99  --inst_restr_to_given                   false
% 1.09/0.99  --inst_activity_threshold               500
% 1.09/0.99  --inst_out_proof                        true
% 1.09/0.99  
% 1.09/0.99  ------ Resolution Options
% 1.09/0.99  
% 1.09/0.99  --resolution_flag                       false
% 1.09/0.99  --res_lit_sel                           adaptive
% 1.09/0.99  --res_lit_sel_side                      none
% 1.09/0.99  --res_ordering                          kbo
% 1.09/0.99  --res_to_prop_solver                    active
% 1.09/0.99  --res_prop_simpl_new                    false
% 1.09/0.99  --res_prop_simpl_given                  true
% 1.09/0.99  --res_passive_queue_type                priority_queues
% 1.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/0.99  --res_passive_queues_freq               [15;5]
% 1.09/0.99  --res_forward_subs                      full
% 1.09/0.99  --res_backward_subs                     full
% 1.09/0.99  --res_forward_subs_resolution           true
% 1.09/0.99  --res_backward_subs_resolution          true
% 1.09/0.99  --res_orphan_elimination                true
% 1.09/0.99  --res_time_limit                        2.
% 1.09/0.99  --res_out_proof                         true
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Options
% 1.09/0.99  
% 1.09/0.99  --superposition_flag                    true
% 1.09/0.99  --sup_passive_queue_type                priority_queues
% 1.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.09/0.99  --demod_completeness_check              fast
% 1.09/0.99  --demod_use_ground                      true
% 1.09/0.99  --sup_to_prop_solver                    passive
% 1.09/0.99  --sup_prop_simpl_new                    true
% 1.09/0.99  --sup_prop_simpl_given                  true
% 1.09/0.99  --sup_fun_splitting                     false
% 1.09/0.99  --sup_smt_interval                      50000
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Simplification Setup
% 1.09/0.99  
% 1.09/0.99  --sup_indices_passive                   []
% 1.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_full_bw                           [BwDemod]
% 1.09/0.99  --sup_immed_triv                        [TrivRules]
% 1.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_immed_bw_main                     []
% 1.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  
% 1.09/0.99  ------ Combination Options
% 1.09/0.99  
% 1.09/0.99  --comb_res_mult                         3
% 1.09/0.99  --comb_sup_mult                         2
% 1.09/0.99  --comb_inst_mult                        10
% 1.09/0.99  
% 1.09/0.99  ------ Debug Options
% 1.09/0.99  
% 1.09/0.99  --dbg_backtrace                         false
% 1.09/0.99  --dbg_dump_prop_clauses                 false
% 1.09/0.99  --dbg_dump_prop_clauses_file            -
% 1.09/0.99  --dbg_out_stat                          false
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  ------ Proving...
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  % SZS status Theorem for theBenchmark.p
% 1.09/0.99  
% 1.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.09/0.99  
% 1.09/0.99  fof(f7,conjecture,(
% 1.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f8,negated_conjecture,(
% 1.09/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.09/0.99    inference(negated_conjecture,[],[f7])).
% 1.09/0.99  
% 1.09/0.99  fof(f16,plain,(
% 1.09/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.09/0.99    inference(ennf_transformation,[],[f8])).
% 1.09/0.99  
% 1.09/0.99  fof(f17,plain,(
% 1.09/0.99    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.09/0.99    inference(flattening,[],[f16])).
% 1.09/0.99  
% 1.09/0.99  fof(f19,plain,(
% 1.09/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK2 != sK3 & k1_funct_1(X1,sK2) = k1_funct_1(X1,sK3) & r2_hidden(sK3,X0) & r2_hidden(sK2,X0))) )),
% 1.09/0.99    introduced(choice_axiom,[])).
% 1.09/0.99  
% 1.09/0.99  fof(f18,plain,(
% 1.09/0.99    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.09/0.99    introduced(choice_axiom,[])).
% 1.09/0.99  
% 1.09/0.99  fof(f20,plain,(
% 1.09/0.99    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).
% 1.09/0.99  
% 1.09/0.99  fof(f31,plain,(
% 1.09/0.99    r2_hidden(sK2,sK0)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f28,plain,(
% 1.09/0.99    v1_funct_2(sK1,sK0,sK0)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f5,axiom,(
% 1.09/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f12,plain,(
% 1.09/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.09/0.99    inference(ennf_transformation,[],[f5])).
% 1.09/0.99  
% 1.09/0.99  fof(f13,plain,(
% 1.09/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.09/0.99    inference(flattening,[],[f12])).
% 1.09/0.99  
% 1.09/0.99  fof(f25,plain,(
% 1.09/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.09/0.99    inference(cnf_transformation,[],[f13])).
% 1.09/0.99  
% 1.09/0.99  fof(f30,plain,(
% 1.09/0.99    v2_funct_1(sK1)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f27,plain,(
% 1.09/0.99    v1_funct_1(sK1)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f29,plain,(
% 1.09/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f32,plain,(
% 1.09/0.99    r2_hidden(sK3,sK0)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f33,plain,(
% 1.09/0.99    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f34,plain,(
% 1.09/0.99    sK2 != sK3),
% 1.09/0.99    inference(cnf_transformation,[],[f20])).
% 1.09/0.99  
% 1.09/0.99  fof(f6,axiom,(
% 1.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f14,plain,(
% 1.09/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.09/0.99    inference(ennf_transformation,[],[f6])).
% 1.09/0.99  
% 1.09/0.99  fof(f15,plain,(
% 1.09/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.09/0.99    inference(flattening,[],[f14])).
% 1.09/0.99  
% 1.09/0.99  fof(f26,plain,(
% 1.09/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.09/0.99    inference(cnf_transformation,[],[f15])).
% 1.09/0.99  
% 1.09/0.99  fof(f3,axiom,(
% 1.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f10,plain,(
% 1.09/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.09/0.99    inference(ennf_transformation,[],[f3])).
% 1.09/0.99  
% 1.09/0.99  fof(f23,plain,(
% 1.09/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.09/0.99    inference(cnf_transformation,[],[f10])).
% 1.09/0.99  
% 1.09/0.99  fof(f1,axiom,(
% 1.09/0.99    v1_xboole_0(k1_xboole_0)),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f21,plain,(
% 1.09/0.99    v1_xboole_0(k1_xboole_0)),
% 1.09/0.99    inference(cnf_transformation,[],[f1])).
% 1.09/0.99  
% 1.09/0.99  fof(f2,axiom,(
% 1.09/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.09/0.99  
% 1.09/0.99  fof(f9,plain,(
% 1.09/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.09/0.99    inference(ennf_transformation,[],[f2])).
% 1.09/0.99  
% 1.09/0.99  fof(f22,plain,(
% 1.09/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.09/0.99    inference(cnf_transformation,[],[f9])).
% 1.09/0.99  
% 1.09/0.99  cnf(c_9,negated_conjecture,
% 1.09/0.99      ( r2_hidden(sK2,sK0) ),
% 1.09/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_12,negated_conjecture,
% 1.09/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 1.09/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_4,plain,
% 1.09/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.09/0.99      | ~ r2_hidden(X3,X1)
% 1.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.09/0.99      | ~ v1_funct_1(X0)
% 1.09/0.99      | ~ v2_funct_1(X0)
% 1.09/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.09/0.99      | k1_xboole_0 = X2 ),
% 1.09/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_10,negated_conjecture,
% 1.09/0.99      ( v2_funct_1(sK1) ),
% 1.09/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_149,plain,
% 1.09/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.09/0.99      | ~ r2_hidden(X3,X1)
% 1.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.09/0.99      | ~ v1_funct_1(X0)
% 1.09/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 1.09/0.99      | sK1 != X0
% 1.09/0.99      | k1_xboole_0 = X2 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_150,plain,
% 1.09/0.99      ( ~ v1_funct_2(sK1,X0,X1)
% 1.09/0.99      | ~ r2_hidden(X2,X0)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.09/0.99      | ~ v1_funct_1(sK1)
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 1.09/0.99      | k1_xboole_0 = X1 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_149]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_13,negated_conjecture,
% 1.09/0.99      ( v1_funct_1(sK1) ),
% 1.09/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_154,plain,
% 1.09/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.09/0.99      | ~ r2_hidden(X2,X0)
% 1.09/0.99      | ~ v1_funct_2(sK1,X0,X1)
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 1.09/0.99      | k1_xboole_0 = X1 ),
% 1.09/0.99      inference(global_propositional_subsumption,
% 1.09/0.99                [status(thm)],
% 1.09/0.99                [c_150,c_13]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_155,plain,
% 1.09/0.99      ( ~ v1_funct_2(sK1,X0,X1)
% 1.09/0.99      | ~ r2_hidden(X2,X0)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 1.09/0.99      | k1_xboole_0 = X1 ),
% 1.09/0.99      inference(renaming,[status(thm)],[c_154]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_201,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,X1)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
% 1.09/0.99      | sK0 != X1
% 1.09/0.99      | sK0 != X2
% 1.09/0.99      | sK1 != sK1
% 1.09/0.99      | k1_xboole_0 = X2 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_155]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_202,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,sK0)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
% 1.09/0.99      | k1_xboole_0 = sK0 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_201]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_11,negated_conjecture,
% 1.09/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.09/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_206,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,sK0)
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
% 1.09/0.99      | k1_xboole_0 = sK0 ),
% 1.09/0.99      inference(global_propositional_subsumption,
% 1.09/0.99                [status(thm)],
% 1.09/0.99                [c_202,c_11]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_252,plain,
% 1.09/0.99      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
% 1.09/0.99      | sK0 != sK0
% 1.09/0.99      | sK0 = k1_xboole_0
% 1.09/0.99      | sK2 != X0 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_206]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_253,plain,
% 1.09/0.99      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 1.09/0.99      | sK0 = k1_xboole_0 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_252]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_301,plain,
% 1.09/0.99      ( sK0 = k1_xboole_0
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2 ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_253]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_8,negated_conjecture,
% 1.09/0.99      ( r2_hidden(sK3,sK0) ),
% 1.09/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_244,plain,
% 1.09/0.99      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
% 1.09/0.99      | sK0 != sK0
% 1.09/0.99      | sK0 = k1_xboole_0
% 1.09/0.99      | sK3 != X0 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_206]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_245,plain,
% 1.09/0.99      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 1.09/0.99      | sK0 = k1_xboole_0 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_244]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_302,plain,
% 1.09/0.99      ( sK0 = k1_xboole_0
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3 ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_245]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_7,negated_conjecture,
% 1.09/0.99      ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
% 1.09/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_306,negated_conjecture,
% 1.09/0.99      ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_421,plain,
% 1.09/0.99      ( sK0 = k1_xboole_0
% 1.09/0.99      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
% 1.09/0.99      inference(light_normalisation,[status(thm)],[c_302,c_306]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_499,plain,
% 1.09/0.99      ( sK0 = k1_xboole_0 | sK3 = sK2 ),
% 1.09/0.99      inference(superposition,[status(thm)],[c_301,c_421]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_311,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_329,plain,
% 1.09/0.99      ( sK2 = sK2 ),
% 1.09/0.99      inference(instantiation,[status(thm)],[c_311]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_6,negated_conjecture,
% 1.09/0.99      ( sK2 != sK3 ),
% 1.09/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_307,negated_conjecture,
% 1.09/0.99      ( sK2 != sK3 ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_314,plain,
% 1.09/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.09/0.99      theory(equality) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_449,plain,
% 1.09/0.99      ( sK3 != X0_45 | sK2 != X0_45 | sK2 = sK3 ),
% 1.09/0.99      inference(instantiation,[status(thm)],[c_314]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_450,plain,
% 1.09/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 1.09/0.99      inference(instantiation,[status(thm)],[c_449]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_559,plain,
% 1.09/0.99      ( sK0 = k1_xboole_0 ),
% 1.09/0.99      inference(global_propositional_subsumption,
% 1.09/0.99                [status(thm)],
% 1.09/0.99                [c_499,c_329,c_307,c_450]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_5,plain,
% 1.09/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 1.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.09/0.99      | ~ v1_funct_1(X0)
% 1.09/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.09/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_182,plain,
% 1.09/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 1.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.09/0.99      | k1_relset_1(X1,X1,X0) = X1
% 1.09/0.99      | sK1 != X0 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_183,plain,
% 1.09/0.99      ( ~ v1_funct_2(sK1,X0,X0)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.09/0.99      | k1_relset_1(X0,X0,sK1) = X0 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_182]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_222,plain,
% 1.09/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.09/0.99      | k1_relset_1(X0,X0,sK1) = X0
% 1.09/0.99      | sK0 != X0
% 1.09/0.99      | sK1 != sK1 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_183]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_223,plain,
% 1.09/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.09/0.99      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_222]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_185,plain,
% 1.09/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 1.09/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.09/0.99      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 1.09/0.99      inference(instantiation,[status(thm)],[c_183]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_225,plain,
% 1.09/0.99      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 1.09/0.99      inference(global_propositional_subsumption,
% 1.09/0.99                [status(thm)],
% 1.09/0.99                [c_223,c_12,c_11,c_185]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_304,plain,
% 1.09/0.99      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_225]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_564,plain,
% 1.09/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 1.09/0.99      inference(demodulation,[status(thm)],[c_559,c_304]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_2,plain,
% 1.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.09/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.09/0.99      inference(cnf_transformation,[],[f23]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_309,plain,
% 1.09/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.09/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_407,plain,
% 1.09/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 1.09/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 1.09/0.99      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_746,plain,
% 1.09/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 1.09/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.09/0.99      inference(superposition,[status(thm)],[c_564,c_407]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_305,negated_conjecture,
% 1.09/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_409,plain,
% 1.09/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.09/0.99      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_563,plain,
% 1.09/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.09/0.99      inference(demodulation,[status(thm)],[c_559,c_409]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_0,plain,
% 1.09/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.09/0.99      inference(cnf_transformation,[],[f21]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_1,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,X1)
% 1.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.09/0.99      | ~ v1_xboole_0(X2) ),
% 1.09/0.99      inference(cnf_transformation,[],[f22]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_134,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,X1)
% 1.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.09/0.99      | k1_xboole_0 != X2 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_135,plain,
% 1.09/0.99      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_134]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_235,plain,
% 1.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.09/0.99      | sK0 != X0
% 1.09/0.99      | sK3 != X1 ),
% 1.09/0.99      inference(resolution_lifted,[status(thm)],[c_135,c_8]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_236,plain,
% 1.09/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.09/0.99      inference(unflattening,[status(thm)],[c_235]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_303,plain,
% 1.09/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.09/0.99      inference(subtyping,[status(esa)],[c_236]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_410,plain,
% 1.09/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.09/0.99      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(c_562,plain,
% 1.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.09/0.99      inference(demodulation,[status(thm)],[c_559,c_410]) ).
% 1.09/0.99  
% 1.09/0.99  cnf(contradiction,plain,
% 1.09/0.99      ( $false ),
% 1.09/0.99      inference(minisat,[status(thm)],[c_746,c_563,c_562]) ).
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.09/0.99  
% 1.09/0.99  ------                               Statistics
% 1.09/0.99  
% 1.09/0.99  ------ General
% 1.09/0.99  
% 1.09/0.99  abstr_ref_over_cycles:                  0
% 1.09/0.99  abstr_ref_under_cycles:                 0
% 1.09/0.99  gc_basic_clause_elim:                   0
% 1.09/0.99  forced_gc_time:                         0
% 1.09/0.99  parsing_time:                           0.015
% 1.09/0.99  unif_index_cands_time:                  0.
% 1.09/0.99  unif_index_add_time:                    0.
% 1.09/0.99  orderings_time:                         0.
% 1.09/0.99  out_proof_time:                         0.009
% 1.09/0.99  total_time:                             0.077
% 1.09/0.99  num_of_symbols:                         51
% 1.09/0.99  num_of_terms:                           1030
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing
% 1.09/0.99  
% 1.09/0.99  num_of_splits:                          0
% 1.09/0.99  num_of_split_atoms:                     0
% 1.09/0.99  num_of_reused_defs:                     0
% 1.09/0.99  num_eq_ax_congr_red:                    7
% 1.09/0.99  num_of_sem_filtered_clauses:            1
% 1.09/0.99  num_of_subtypes:                        3
% 1.09/0.99  monotx_restored_types:                  0
% 1.09/0.99  sat_num_of_epr_types:                   0
% 1.09/0.99  sat_num_of_non_cyclic_types:            0
% 1.09/0.99  sat_guarded_non_collapsed_types:        0
% 1.09/0.99  num_pure_diseq_elim:                    0
% 1.09/0.99  simp_replaced_by:                       0
% 1.09/0.99  res_preprocessed:                       64
% 1.09/0.99  prep_upred:                             0
% 1.09/0.99  prep_unflattend:                        12
% 1.09/0.99  smt_new_axioms:                         0
% 1.09/0.99  pred_elim_cands:                        1
% 1.09/0.99  pred_elim:                              5
% 1.09/0.99  pred_elim_cl:                           5
% 1.09/0.99  pred_elim_cycles:                       7
% 1.09/0.99  merged_defs:                            0
% 1.09/0.99  merged_defs_ncl:                        0
% 1.09/0.99  bin_hyper_res:                          0
% 1.09/0.99  prep_cycles:                            4
% 1.09/0.99  pred_elim_time:                         0.003
% 1.09/0.99  splitting_time:                         0.
% 1.09/0.99  sem_filter_time:                        0.
% 1.09/0.99  monotx_time:                            0.
% 1.09/0.99  subtype_inf_time:                       0.
% 1.09/0.99  
% 1.09/0.99  ------ Problem properties
% 1.09/0.99  
% 1.09/0.99  clauses:                                9
% 1.09/0.99  conjectures:                            3
% 1.09/0.99  epr:                                    1
% 1.09/0.99  horn:                                   7
% 1.09/0.99  ground:                                 7
% 1.09/0.99  unary:                                  5
% 1.09/0.99  binary:                                 4
% 1.09/0.99  lits:                                   13
% 1.09/0.99  lits_eq:                                8
% 1.09/0.99  fd_pure:                                0
% 1.09/0.99  fd_pseudo:                              0
% 1.09/0.99  fd_cond:                                0
% 1.09/0.99  fd_pseudo_cond:                         0
% 1.09/0.99  ac_symbols:                             0
% 1.09/0.99  
% 1.09/0.99  ------ Propositional Solver
% 1.09/0.99  
% 1.09/0.99  prop_solver_calls:                      27
% 1.09/0.99  prop_fast_solver_calls:                 295
% 1.09/0.99  smt_solver_calls:                       0
% 1.09/0.99  smt_fast_solver_calls:                  0
% 1.09/0.99  prop_num_of_clauses:                    262
% 1.09/0.99  prop_preprocess_simplified:             1326
% 1.09/0.99  prop_fo_subsumed:                       5
% 1.09/0.99  prop_solver_time:                       0.
% 1.09/0.99  smt_solver_time:                        0.
% 1.09/0.99  smt_fast_solver_time:                   0.
% 1.09/0.99  prop_fast_solver_time:                  0.
% 1.09/0.99  prop_unsat_core_time:                   0.
% 1.09/0.99  
% 1.09/0.99  ------ QBF
% 1.09/0.99  
% 1.09/0.99  qbf_q_res:                              0
% 1.09/0.99  qbf_num_tautologies:                    0
% 1.09/0.99  qbf_prep_cycles:                        0
% 1.09/0.99  
% 1.09/0.99  ------ BMC1
% 1.09/0.99  
% 1.09/0.99  bmc1_current_bound:                     -1
% 1.09/0.99  bmc1_last_solved_bound:                 -1
% 1.09/0.99  bmc1_unsat_core_size:                   -1
% 1.09/0.99  bmc1_unsat_core_parents_size:           -1
% 1.09/0.99  bmc1_merge_next_fun:                    0
% 1.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.09/0.99  
% 1.09/0.99  ------ Instantiation
% 1.09/0.99  
% 1.09/0.99  inst_num_of_clauses:                    86
% 1.09/0.99  inst_num_in_passive:                    22
% 1.09/0.99  inst_num_in_active:                     62
% 1.09/0.99  inst_num_in_unprocessed:                2
% 1.09/0.99  inst_num_of_loops:                      70
% 1.09/0.99  inst_num_of_learning_restarts:          0
% 1.09/0.99  inst_num_moves_active_passive:          3
% 1.09/0.99  inst_lit_activity:                      0
% 1.09/0.99  inst_lit_activity_moves:                0
% 1.09/0.99  inst_num_tautologies:                   0
% 1.09/0.99  inst_num_prop_implied:                  0
% 1.09/0.99  inst_num_existing_simplified:           0
% 1.09/0.99  inst_num_eq_res_simplified:             0
% 1.09/0.99  inst_num_child_elim:                    0
% 1.09/0.99  inst_num_of_dismatching_blockings:      11
% 1.09/0.99  inst_num_of_non_proper_insts:           61
% 1.09/0.99  inst_num_of_duplicates:                 0
% 1.09/0.99  inst_inst_num_from_inst_to_res:         0
% 1.09/0.99  inst_dismatching_checking_time:         0.
% 1.09/0.99  
% 1.09/0.99  ------ Resolution
% 1.09/0.99  
% 1.09/0.99  res_num_of_clauses:                     0
% 1.09/0.99  res_num_in_passive:                     0
% 1.09/0.99  res_num_in_active:                      0
% 1.09/0.99  res_num_of_loops:                       68
% 1.09/0.99  res_forward_subset_subsumed:            12
% 1.09/0.99  res_backward_subset_subsumed:           0
% 1.09/0.99  res_forward_subsumed:                   0
% 1.09/0.99  res_backward_subsumed:                  0
% 1.09/0.99  res_forward_subsumption_resolution:     0
% 1.09/0.99  res_backward_subsumption_resolution:    0
% 1.09/0.99  res_clause_to_clause_subsumption:       13
% 1.09/0.99  res_orphan_elimination:                 0
% 1.09/0.99  res_tautology_del:                      10
% 1.09/0.99  res_num_eq_res_simplified:              0
% 1.09/0.99  res_num_sel_changes:                    0
% 1.09/0.99  res_moves_from_active_to_pass:          0
% 1.09/0.99  
% 1.09/0.99  ------ Superposition
% 1.09/0.99  
% 1.09/0.99  sup_time_total:                         0.
% 1.09/0.99  sup_time_generating:                    0.
% 1.09/0.99  sup_time_sim_full:                      0.
% 1.09/0.99  sup_time_sim_immed:                     0.
% 1.09/0.99  
% 1.09/0.99  sup_num_of_clauses:                     12
% 1.09/0.99  sup_num_in_active:                      8
% 1.09/0.99  sup_num_in_passive:                     4
% 1.09/0.99  sup_num_of_loops:                       13
% 1.09/0.99  sup_fw_superposition:                   2
% 1.09/0.99  sup_bw_superposition:                   4
% 1.09/0.99  sup_immediate_simplified:               0
% 1.09/0.99  sup_given_eliminated:                   0
% 1.09/0.99  comparisons_done:                       0
% 1.09/0.99  comparisons_avoided:                    6
% 1.09/0.99  
% 1.09/0.99  ------ Simplifications
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  sim_fw_subset_subsumed:                 0
% 1.09/0.99  sim_bw_subset_subsumed:                 2
% 1.09/0.99  sim_fw_subsumed:                        0
% 1.09/0.99  sim_bw_subsumed:                        0
% 1.09/0.99  sim_fw_subsumption_res:                 0
% 1.09/0.99  sim_bw_subsumption_res:                 0
% 1.09/0.99  sim_tautology_del:                      0
% 1.09/0.99  sim_eq_tautology_del:                   0
% 1.09/0.99  sim_eq_res_simp:                        0
% 1.09/0.99  sim_fw_demodulated:                     0
% 1.09/0.99  sim_bw_demodulated:                     4
% 1.09/0.99  sim_light_normalised:                   1
% 1.09/0.99  sim_joinable_taut:                      0
% 1.09/0.99  sim_joinable_simp:                      0
% 1.09/0.99  sim_ac_normalised:                      0
% 1.09/0.99  sim_smt_subsumption:                    0
% 1.09/0.99  
%------------------------------------------------------------------------------
