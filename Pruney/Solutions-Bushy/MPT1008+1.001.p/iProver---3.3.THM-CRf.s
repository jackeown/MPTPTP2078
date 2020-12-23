%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1008+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:38 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 185 expanded)
%              Number of clauses        :   44 (  69 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 ( 722 expanded)
%              Number of equality atoms :  135 ( 349 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_192,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_193,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_439,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))
    | k2_relset_1(X0_44,X1_44,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_580,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_439])).

cnf(c_10,negated_conjecture,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_441,negated_conjecture,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_663,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_580,c_441])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_201,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_202,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_438,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))
    | k1_relset_1(X0_44,X1_44,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_577,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_438])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_210,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_211,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_369,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | k1_tarski(sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2
    | sK1 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_211])).

cnf(c_370,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_371,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))
    | k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_11])).

cnf(c_372,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_421,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_372])).

cnf(c_435,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(sK0) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_628,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_577,c_435])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_tarski(X1) != k1_relat_1(X0)
    | k1_tarski(k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_154,plain,
    ( ~ v1_relat_1(X0)
    | k1_tarski(X1) != k1_relat_1(X0)
    | k1_tarski(k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_155,plain,
    ( ~ v1_relat_1(sK2)
    | k1_tarski(X0) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_tarski(X3) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X3)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_155])).

cnf(c_174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_tarski(X2) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_311,plain,
    ( k1_tarski(X0) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_174])).

cnf(c_422,plain,
    ( k1_tarski(X0) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_311])).

cnf(c_434,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))
    | k1_tarski(X0_45) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_45)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_443,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_434])).

cnf(c_560,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_447,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_559,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_442,plain,
    ( k1_tarski(X0_45) != k1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0_45)) = k2_relat_1(sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_434])).

cnf(c_478,plain,
    ( ~ sP0_iProver_split
    | k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_444,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_434])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_663,c_628,c_560,c_559,c_478,c_444])).


%------------------------------------------------------------------------------
