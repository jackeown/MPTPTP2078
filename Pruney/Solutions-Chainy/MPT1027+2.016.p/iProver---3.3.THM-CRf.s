%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:19 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 578 expanded)
%              Number of clauses        :   81 ( 177 expanded)
%              Number of leaves         :   13 ( 119 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 (2692 expanded)
%              Number of equality atoms :  214 ( 818 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & k1_relset_1(sK0,sK1,sK2) = sK0
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & k1_relset_1(sK0,sK1,sK2) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_699,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_96,negated_conjecture,
    ( ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_22,c_21])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK1 != X2
    | sK0 != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_96])).

cnf(c_324,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) != sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_20,negated_conjecture,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_326,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_21,c_20])).

cnf(c_719,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_699,c_326])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_720,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_719,c_0])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_701,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1301,plain,
    ( k9_relat_1(k6_relat_1(k1_xboole_0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_720,c_701])).

cnf(c_6,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1303,plain,
    ( k9_relat_1(k1_xboole_0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1301,c_6])).

cnf(c_3,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1304,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1303,c_3])).

cnf(c_10,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_247,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_96])).

cnf(c_248,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_697,plain,
    ( sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_766,plain,
    ( sK0 = k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_697,c_326])).

cnf(c_767,plain,
    ( sK0 = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_766])).

cnf(c_768,plain,
    ( sK0 = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_767,c_0])).

cnf(c_5,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_61,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_62,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_183,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_184,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_221,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_184])).

cnf(c_222,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_96,c_222])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_352])).

cnf(c_477,plain,
    ( sP0_iProver_split
    | k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_409])).

cnf(c_688,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_737,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_688,c_326])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_835,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_836,plain,
    ( k1_relat_1(sK2) = sK0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_194,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_194])).

cnf(c_210,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_698,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_817,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_818,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_849,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_24,c_818])).

cnf(c_476,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_409])).

cnf(c_689,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_854,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_689])).

cnf(c_832,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_896,plain,
    ( k2_relat_1(sK2) != k2_relat_1(X0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_898,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_486,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_897,plain,
    ( k2_relat_1(sK2) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_899,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_834,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_903,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_905,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_487,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_904,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_906,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_1030,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1031,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1038,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1039,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1097,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_5,c_4,c_61,c_62,c_737,c_836,c_854,c_898,c_899,c_905,c_906,c_1031,c_1039])).

cnf(c_1313,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1304,c_1097])).

cnf(c_1346,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1313])).

cnf(c_1318,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1304,c_720])).

cnf(c_1348,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1346,c_1318])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/0.99  
% 1.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/0.99  
% 1.58/0.99  ------  iProver source info
% 1.58/0.99  
% 1.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/0.99  git: non_committed_changes: false
% 1.58/0.99  git: last_make_outside_of_git: false
% 1.58/0.99  
% 1.58/0.99  ------ 
% 1.58/0.99  
% 1.58/0.99  ------ Input Options
% 1.58/0.99  
% 1.58/0.99  --out_options                           all
% 1.58/0.99  --tptp_safe_out                         true
% 1.58/0.99  --problem_path                          ""
% 1.58/0.99  --include_path                          ""
% 1.58/0.99  --clausifier                            res/vclausify_rel
% 1.58/0.99  --clausifier_options                    --mode clausify
% 1.58/0.99  --stdin                                 false
% 1.58/0.99  --stats_out                             all
% 1.58/0.99  
% 1.58/0.99  ------ General Options
% 1.58/0.99  
% 1.58/0.99  --fof                                   false
% 1.58/0.99  --time_out_real                         305.
% 1.58/0.99  --time_out_virtual                      -1.
% 1.58/0.99  --symbol_type_check                     false
% 1.58/0.99  --clausify_out                          false
% 1.58/0.99  --sig_cnt_out                           false
% 1.58/0.99  --trig_cnt_out                          false
% 1.58/0.99  --trig_cnt_out_tolerance                1.
% 1.58/0.99  --trig_cnt_out_sk_spl                   false
% 1.58/0.99  --abstr_cl_out                          false
% 1.58/0.99  
% 1.58/0.99  ------ Global Options
% 1.58/0.99  
% 1.58/0.99  --schedule                              default
% 1.58/0.99  --add_important_lit                     false
% 1.58/0.99  --prop_solver_per_cl                    1000
% 1.58/0.99  --min_unsat_core                        false
% 1.58/0.99  --soft_assumptions                      false
% 1.58/0.99  --soft_lemma_size                       3
% 1.58/0.99  --prop_impl_unit_size                   0
% 1.58/0.99  --prop_impl_unit                        []
% 1.58/0.99  --share_sel_clauses                     true
% 1.58/0.99  --reset_solvers                         false
% 1.58/0.99  --bc_imp_inh                            [conj_cone]
% 1.58/0.99  --conj_cone_tolerance                   3.
% 1.58/0.99  --extra_neg_conj                        none
% 1.58/0.99  --large_theory_mode                     true
% 1.58/0.99  --prolific_symb_bound                   200
% 1.58/0.99  --lt_threshold                          2000
% 1.58/0.99  --clause_weak_htbl                      true
% 1.58/0.99  --gc_record_bc_elim                     false
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing Options
% 1.58/0.99  
% 1.58/0.99  --preprocessing_flag                    true
% 1.58/0.99  --time_out_prep_mult                    0.1
% 1.58/0.99  --splitting_mode                        input
% 1.58/0.99  --splitting_grd                         true
% 1.58/0.99  --splitting_cvd                         false
% 1.58/0.99  --splitting_cvd_svl                     false
% 1.58/0.99  --splitting_nvd                         32
% 1.58/0.99  --sub_typing                            true
% 1.58/0.99  --prep_gs_sim                           true
% 1.58/0.99  --prep_unflatten                        true
% 1.58/0.99  --prep_res_sim                          true
% 1.58/0.99  --prep_upred                            true
% 1.58/0.99  --prep_sem_filter                       exhaustive
% 1.58/0.99  --prep_sem_filter_out                   false
% 1.58/0.99  --pred_elim                             true
% 1.58/0.99  --res_sim_input                         true
% 1.58/0.99  --eq_ax_congr_red                       true
% 1.58/0.99  --pure_diseq_elim                       true
% 1.58/0.99  --brand_transform                       false
% 1.58/0.99  --non_eq_to_eq                          false
% 1.58/0.99  --prep_def_merge                        true
% 1.58/0.99  --prep_def_merge_prop_impl              false
% 1.58/0.99  --prep_def_merge_mbd                    true
% 1.58/0.99  --prep_def_merge_tr_red                 false
% 1.58/0.99  --prep_def_merge_tr_cl                  false
% 1.58/0.99  --smt_preprocessing                     true
% 1.58/0.99  --smt_ac_axioms                         fast
% 1.58/0.99  --preprocessed_out                      false
% 1.58/0.99  --preprocessed_stats                    false
% 1.58/0.99  
% 1.58/0.99  ------ Abstraction refinement Options
% 1.58/0.99  
% 1.58/0.99  --abstr_ref                             []
% 1.58/0.99  --abstr_ref_prep                        false
% 1.58/0.99  --abstr_ref_until_sat                   false
% 1.58/0.99  --abstr_ref_sig_restrict                funpre
% 1.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/0.99  --abstr_ref_under                       []
% 1.58/0.99  
% 1.58/0.99  ------ SAT Options
% 1.58/0.99  
% 1.58/0.99  --sat_mode                              false
% 1.58/0.99  --sat_fm_restart_options                ""
% 1.58/0.99  --sat_gr_def                            false
% 1.58/0.99  --sat_epr_types                         true
% 1.58/0.99  --sat_non_cyclic_types                  false
% 1.58/0.99  --sat_finite_models                     false
% 1.58/0.99  --sat_fm_lemmas                         false
% 1.58/0.99  --sat_fm_prep                           false
% 1.58/0.99  --sat_fm_uc_incr                        true
% 1.58/0.99  --sat_out_model                         small
% 1.58/0.99  --sat_out_clauses                       false
% 1.58/0.99  
% 1.58/0.99  ------ QBF Options
% 1.58/0.99  
% 1.58/0.99  --qbf_mode                              false
% 1.58/0.99  --qbf_elim_univ                         false
% 1.58/0.99  --qbf_dom_inst                          none
% 1.58/0.99  --qbf_dom_pre_inst                      false
% 1.58/0.99  --qbf_sk_in                             false
% 1.58/0.99  --qbf_pred_elim                         true
% 1.58/0.99  --qbf_split                             512
% 1.58/0.99  
% 1.58/0.99  ------ BMC1 Options
% 1.58/0.99  
% 1.58/0.99  --bmc1_incremental                      false
% 1.58/0.99  --bmc1_axioms                           reachable_all
% 1.58/0.99  --bmc1_min_bound                        0
% 1.58/0.99  --bmc1_max_bound                        -1
% 1.58/0.99  --bmc1_max_bound_default                -1
% 1.58/0.99  --bmc1_symbol_reachability              true
% 1.58/0.99  --bmc1_property_lemmas                  false
% 1.58/0.99  --bmc1_k_induction                      false
% 1.58/0.99  --bmc1_non_equiv_states                 false
% 1.58/0.99  --bmc1_deadlock                         false
% 1.58/0.99  --bmc1_ucm                              false
% 1.58/0.99  --bmc1_add_unsat_core                   none
% 1.58/1.00  --bmc1_unsat_core_children              false
% 1.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.00  --bmc1_out_stat                         full
% 1.58/1.00  --bmc1_ground_init                      false
% 1.58/1.00  --bmc1_pre_inst_next_state              false
% 1.58/1.00  --bmc1_pre_inst_state                   false
% 1.58/1.00  --bmc1_pre_inst_reach_state             false
% 1.58/1.00  --bmc1_out_unsat_core                   false
% 1.58/1.00  --bmc1_aig_witness_out                  false
% 1.58/1.00  --bmc1_verbose                          false
% 1.58/1.00  --bmc1_dump_clauses_tptp                false
% 1.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.00  --bmc1_dump_file                        -
% 1.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.00  --bmc1_ucm_extend_mode                  1
% 1.58/1.00  --bmc1_ucm_init_mode                    2
% 1.58/1.00  --bmc1_ucm_cone_mode                    none
% 1.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.00  --bmc1_ucm_relax_model                  4
% 1.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.00  --bmc1_ucm_layered_model                none
% 1.58/1.00  --bmc1_ucm_max_lemma_size               10
% 1.58/1.00  
% 1.58/1.00  ------ AIG Options
% 1.58/1.00  
% 1.58/1.00  --aig_mode                              false
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation Options
% 1.58/1.00  
% 1.58/1.00  --instantiation_flag                    true
% 1.58/1.00  --inst_sos_flag                         false
% 1.58/1.00  --inst_sos_phase                        true
% 1.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel_side                     num_symb
% 1.58/1.00  --inst_solver_per_active                1400
% 1.58/1.00  --inst_solver_calls_frac                1.
% 1.58/1.00  --inst_passive_queue_type               priority_queues
% 1.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.00  --inst_passive_queues_freq              [25;2]
% 1.58/1.00  --inst_dismatching                      true
% 1.58/1.00  --inst_eager_unprocessed_to_passive     true
% 1.58/1.00  --inst_prop_sim_given                   true
% 1.58/1.00  --inst_prop_sim_new                     false
% 1.58/1.00  --inst_subs_new                         false
% 1.58/1.00  --inst_eq_res_simp                      false
% 1.58/1.00  --inst_subs_given                       false
% 1.58/1.00  --inst_orphan_elimination               true
% 1.58/1.00  --inst_learning_loop_flag               true
% 1.58/1.00  --inst_learning_start                   3000
% 1.58/1.00  --inst_learning_factor                  2
% 1.58/1.00  --inst_start_prop_sim_after_learn       3
% 1.58/1.00  --inst_sel_renew                        solver
% 1.58/1.00  --inst_lit_activity_flag                true
% 1.58/1.00  --inst_restr_to_given                   false
% 1.58/1.00  --inst_activity_threshold               500
% 1.58/1.00  --inst_out_proof                        true
% 1.58/1.00  
% 1.58/1.00  ------ Resolution Options
% 1.58/1.00  
% 1.58/1.00  --resolution_flag                       true
% 1.58/1.00  --res_lit_sel                           adaptive
% 1.58/1.00  --res_lit_sel_side                      none
% 1.58/1.00  --res_ordering                          kbo
% 1.58/1.00  --res_to_prop_solver                    active
% 1.58/1.00  --res_prop_simpl_new                    false
% 1.58/1.00  --res_prop_simpl_given                  true
% 1.58/1.00  --res_passive_queue_type                priority_queues
% 1.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.00  --res_passive_queues_freq               [15;5]
% 1.58/1.00  --res_forward_subs                      full
% 1.58/1.00  --res_backward_subs                     full
% 1.58/1.00  --res_forward_subs_resolution           true
% 1.58/1.00  --res_backward_subs_resolution          true
% 1.58/1.00  --res_orphan_elimination                true
% 1.58/1.00  --res_time_limit                        2.
% 1.58/1.00  --res_out_proof                         true
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Options
% 1.58/1.00  
% 1.58/1.00  --superposition_flag                    true
% 1.58/1.00  --sup_passive_queue_type                priority_queues
% 1.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.00  --demod_completeness_check              fast
% 1.58/1.00  --demod_use_ground                      true
% 1.58/1.00  --sup_to_prop_solver                    passive
% 1.58/1.00  --sup_prop_simpl_new                    true
% 1.58/1.00  --sup_prop_simpl_given                  true
% 1.58/1.00  --sup_fun_splitting                     false
% 1.58/1.00  --sup_smt_interval                      50000
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Simplification Setup
% 1.58/1.00  
% 1.58/1.00  --sup_indices_passive                   []
% 1.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_full_bw                           [BwDemod]
% 1.58/1.00  --sup_immed_triv                        [TrivRules]
% 1.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_immed_bw_main                     []
% 1.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  
% 1.58/1.00  ------ Combination Options
% 1.58/1.00  
% 1.58/1.00  --comb_res_mult                         3
% 1.58/1.00  --comb_sup_mult                         2
% 1.58/1.00  --comb_inst_mult                        10
% 1.58/1.00  
% 1.58/1.00  ------ Debug Options
% 1.58/1.00  
% 1.58/1.00  --dbg_backtrace                         false
% 1.58/1.00  --dbg_dump_prop_clauses                 false
% 1.58/1.00  --dbg_dump_prop_clauses_file            -
% 1.58/1.00  --dbg_out_stat                          false
% 1.58/1.00  ------ Parsing...
% 1.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.58/1.00  ------ Proving...
% 1.58/1.00  ------ Problem Properties 
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  clauses                                 23
% 1.58/1.00  conjectures                             2
% 1.58/1.00  EPR                                     1
% 1.58/1.00  Horn                                    19
% 1.58/1.00  unary                                   9
% 1.58/1.00  binary                                  7
% 1.58/1.00  lits                                    48
% 1.58/1.00  lits eq                                 27
% 1.58/1.00  fd_pure                                 0
% 1.58/1.00  fd_pseudo                               0
% 1.58/1.00  fd_cond                                 1
% 1.58/1.00  fd_pseudo_cond                          0
% 1.58/1.00  AC symbols                              0
% 1.58/1.00  
% 1.58/1.00  ------ Schedule dynamic 5 is on 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  ------ 
% 1.58/1.00  Current options:
% 1.58/1.00  ------ 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options
% 1.58/1.00  
% 1.58/1.00  --out_options                           all
% 1.58/1.00  --tptp_safe_out                         true
% 1.58/1.00  --problem_path                          ""
% 1.58/1.00  --include_path                          ""
% 1.58/1.00  --clausifier                            res/vclausify_rel
% 1.58/1.00  --clausifier_options                    --mode clausify
% 1.58/1.00  --stdin                                 false
% 1.58/1.00  --stats_out                             all
% 1.58/1.00  
% 1.58/1.00  ------ General Options
% 1.58/1.00  
% 1.58/1.00  --fof                                   false
% 1.58/1.00  --time_out_real                         305.
% 1.58/1.00  --time_out_virtual                      -1.
% 1.58/1.00  --symbol_type_check                     false
% 1.58/1.00  --clausify_out                          false
% 1.58/1.00  --sig_cnt_out                           false
% 1.58/1.00  --trig_cnt_out                          false
% 1.58/1.00  --trig_cnt_out_tolerance                1.
% 1.58/1.00  --trig_cnt_out_sk_spl                   false
% 1.58/1.00  --abstr_cl_out                          false
% 1.58/1.00  
% 1.58/1.00  ------ Global Options
% 1.58/1.00  
% 1.58/1.00  --schedule                              default
% 1.58/1.00  --add_important_lit                     false
% 1.58/1.00  --prop_solver_per_cl                    1000
% 1.58/1.00  --min_unsat_core                        false
% 1.58/1.00  --soft_assumptions                      false
% 1.58/1.00  --soft_lemma_size                       3
% 1.58/1.00  --prop_impl_unit_size                   0
% 1.58/1.00  --prop_impl_unit                        []
% 1.58/1.00  --share_sel_clauses                     true
% 1.58/1.00  --reset_solvers                         false
% 1.58/1.00  --bc_imp_inh                            [conj_cone]
% 1.58/1.00  --conj_cone_tolerance                   3.
% 1.58/1.00  --extra_neg_conj                        none
% 1.58/1.00  --large_theory_mode                     true
% 1.58/1.00  --prolific_symb_bound                   200
% 1.58/1.00  --lt_threshold                          2000
% 1.58/1.00  --clause_weak_htbl                      true
% 1.58/1.00  --gc_record_bc_elim                     false
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing Options
% 1.58/1.00  
% 1.58/1.00  --preprocessing_flag                    true
% 1.58/1.00  --time_out_prep_mult                    0.1
% 1.58/1.00  --splitting_mode                        input
% 1.58/1.00  --splitting_grd                         true
% 1.58/1.00  --splitting_cvd                         false
% 1.58/1.00  --splitting_cvd_svl                     false
% 1.58/1.00  --splitting_nvd                         32
% 1.58/1.00  --sub_typing                            true
% 1.58/1.00  --prep_gs_sim                           true
% 1.58/1.00  --prep_unflatten                        true
% 1.58/1.00  --prep_res_sim                          true
% 1.58/1.00  --prep_upred                            true
% 1.58/1.00  --prep_sem_filter                       exhaustive
% 1.58/1.00  --prep_sem_filter_out                   false
% 1.58/1.00  --pred_elim                             true
% 1.58/1.00  --res_sim_input                         true
% 1.58/1.00  --eq_ax_congr_red                       true
% 1.58/1.00  --pure_diseq_elim                       true
% 1.58/1.00  --brand_transform                       false
% 1.58/1.00  --non_eq_to_eq                          false
% 1.58/1.00  --prep_def_merge                        true
% 1.58/1.00  --prep_def_merge_prop_impl              false
% 1.58/1.00  --prep_def_merge_mbd                    true
% 1.58/1.00  --prep_def_merge_tr_red                 false
% 1.58/1.00  --prep_def_merge_tr_cl                  false
% 1.58/1.00  --smt_preprocessing                     true
% 1.58/1.00  --smt_ac_axioms                         fast
% 1.58/1.00  --preprocessed_out                      false
% 1.58/1.00  --preprocessed_stats                    false
% 1.58/1.00  
% 1.58/1.00  ------ Abstraction refinement Options
% 1.58/1.00  
% 1.58/1.00  --abstr_ref                             []
% 1.58/1.00  --abstr_ref_prep                        false
% 1.58/1.00  --abstr_ref_until_sat                   false
% 1.58/1.00  --abstr_ref_sig_restrict                funpre
% 1.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.00  --abstr_ref_under                       []
% 1.58/1.00  
% 1.58/1.00  ------ SAT Options
% 1.58/1.00  
% 1.58/1.00  --sat_mode                              false
% 1.58/1.00  --sat_fm_restart_options                ""
% 1.58/1.00  --sat_gr_def                            false
% 1.58/1.00  --sat_epr_types                         true
% 1.58/1.00  --sat_non_cyclic_types                  false
% 1.58/1.00  --sat_finite_models                     false
% 1.58/1.00  --sat_fm_lemmas                         false
% 1.58/1.00  --sat_fm_prep                           false
% 1.58/1.00  --sat_fm_uc_incr                        true
% 1.58/1.00  --sat_out_model                         small
% 1.58/1.00  --sat_out_clauses                       false
% 1.58/1.00  
% 1.58/1.00  ------ QBF Options
% 1.58/1.00  
% 1.58/1.00  --qbf_mode                              false
% 1.58/1.00  --qbf_elim_univ                         false
% 1.58/1.00  --qbf_dom_inst                          none
% 1.58/1.00  --qbf_dom_pre_inst                      false
% 1.58/1.00  --qbf_sk_in                             false
% 1.58/1.00  --qbf_pred_elim                         true
% 1.58/1.00  --qbf_split                             512
% 1.58/1.00  
% 1.58/1.00  ------ BMC1 Options
% 1.58/1.00  
% 1.58/1.00  --bmc1_incremental                      false
% 1.58/1.00  --bmc1_axioms                           reachable_all
% 1.58/1.00  --bmc1_min_bound                        0
% 1.58/1.00  --bmc1_max_bound                        -1
% 1.58/1.00  --bmc1_max_bound_default                -1
% 1.58/1.00  --bmc1_symbol_reachability              true
% 1.58/1.00  --bmc1_property_lemmas                  false
% 1.58/1.00  --bmc1_k_induction                      false
% 1.58/1.00  --bmc1_non_equiv_states                 false
% 1.58/1.00  --bmc1_deadlock                         false
% 1.58/1.00  --bmc1_ucm                              false
% 1.58/1.00  --bmc1_add_unsat_core                   none
% 1.58/1.00  --bmc1_unsat_core_children              false
% 1.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.00  --bmc1_out_stat                         full
% 1.58/1.00  --bmc1_ground_init                      false
% 1.58/1.00  --bmc1_pre_inst_next_state              false
% 1.58/1.00  --bmc1_pre_inst_state                   false
% 1.58/1.00  --bmc1_pre_inst_reach_state             false
% 1.58/1.00  --bmc1_out_unsat_core                   false
% 1.58/1.00  --bmc1_aig_witness_out                  false
% 1.58/1.00  --bmc1_verbose                          false
% 1.58/1.00  --bmc1_dump_clauses_tptp                false
% 1.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.00  --bmc1_dump_file                        -
% 1.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.00  --bmc1_ucm_extend_mode                  1
% 1.58/1.00  --bmc1_ucm_init_mode                    2
% 1.58/1.00  --bmc1_ucm_cone_mode                    none
% 1.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.00  --bmc1_ucm_relax_model                  4
% 1.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.00  --bmc1_ucm_layered_model                none
% 1.58/1.00  --bmc1_ucm_max_lemma_size               10
% 1.58/1.00  
% 1.58/1.00  ------ AIG Options
% 1.58/1.00  
% 1.58/1.00  --aig_mode                              false
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation Options
% 1.58/1.00  
% 1.58/1.00  --instantiation_flag                    true
% 1.58/1.00  --inst_sos_flag                         false
% 1.58/1.00  --inst_sos_phase                        true
% 1.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel_side                     none
% 1.58/1.00  --inst_solver_per_active                1400
% 1.58/1.00  --inst_solver_calls_frac                1.
% 1.58/1.00  --inst_passive_queue_type               priority_queues
% 1.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.00  --inst_passive_queues_freq              [25;2]
% 1.58/1.00  --inst_dismatching                      true
% 1.58/1.00  --inst_eager_unprocessed_to_passive     true
% 1.58/1.00  --inst_prop_sim_given                   true
% 1.58/1.00  --inst_prop_sim_new                     false
% 1.58/1.00  --inst_subs_new                         false
% 1.58/1.00  --inst_eq_res_simp                      false
% 1.58/1.00  --inst_subs_given                       false
% 1.58/1.00  --inst_orphan_elimination               true
% 1.58/1.00  --inst_learning_loop_flag               true
% 1.58/1.00  --inst_learning_start                   3000
% 1.58/1.00  --inst_learning_factor                  2
% 1.58/1.00  --inst_start_prop_sim_after_learn       3
% 1.58/1.00  --inst_sel_renew                        solver
% 1.58/1.00  --inst_lit_activity_flag                true
% 1.58/1.00  --inst_restr_to_given                   false
% 1.58/1.00  --inst_activity_threshold               500
% 1.58/1.00  --inst_out_proof                        true
% 1.58/1.00  
% 1.58/1.00  ------ Resolution Options
% 1.58/1.00  
% 1.58/1.00  --resolution_flag                       false
% 1.58/1.00  --res_lit_sel                           adaptive
% 1.58/1.00  --res_lit_sel_side                      none
% 1.58/1.00  --res_ordering                          kbo
% 1.58/1.00  --res_to_prop_solver                    active
% 1.58/1.00  --res_prop_simpl_new                    false
% 1.58/1.00  --res_prop_simpl_given                  true
% 1.58/1.00  --res_passive_queue_type                priority_queues
% 1.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.00  --res_passive_queues_freq               [15;5]
% 1.58/1.00  --res_forward_subs                      full
% 1.58/1.00  --res_backward_subs                     full
% 1.58/1.00  --res_forward_subs_resolution           true
% 1.58/1.00  --res_backward_subs_resolution          true
% 1.58/1.00  --res_orphan_elimination                true
% 1.58/1.00  --res_time_limit                        2.
% 1.58/1.00  --res_out_proof                         true
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Options
% 1.58/1.00  
% 1.58/1.00  --superposition_flag                    true
% 1.58/1.00  --sup_passive_queue_type                priority_queues
% 1.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.00  --demod_completeness_check              fast
% 1.58/1.00  --demod_use_ground                      true
% 1.58/1.00  --sup_to_prop_solver                    passive
% 1.58/1.00  --sup_prop_simpl_new                    true
% 1.58/1.00  --sup_prop_simpl_given                  true
% 1.58/1.00  --sup_fun_splitting                     false
% 1.58/1.00  --sup_smt_interval                      50000
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Simplification Setup
% 1.58/1.00  
% 1.58/1.00  --sup_indices_passive                   []
% 1.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_full_bw                           [BwDemod]
% 1.58/1.00  --sup_immed_triv                        [TrivRules]
% 1.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_immed_bw_main                     []
% 1.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  
% 1.58/1.00  ------ Combination Options
% 1.58/1.00  
% 1.58/1.00  --comb_res_mult                         3
% 1.58/1.00  --comb_sup_mult                         2
% 1.58/1.00  --comb_inst_mult                        10
% 1.58/1.00  
% 1.58/1.00  ------ Debug Options
% 1.58/1.00  
% 1.58/1.00  --dbg_backtrace                         false
% 1.58/1.00  --dbg_dump_prop_clauses                 false
% 1.58/1.00  --dbg_dump_prop_clauses_file            -
% 1.58/1.00  --dbg_out_stat                          false
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  ------ Proving...
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  % SZS status Theorem for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00   Resolution empty clause
% 1.58/1.00  
% 1.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  fof(f10,conjecture,(
% 1.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f11,negated_conjecture,(
% 1.58/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.58/1.00    inference(negated_conjecture,[],[f10])).
% 1.58/1.00  
% 1.58/1.00  fof(f19,plain,(
% 1.58/1.00    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.58/1.00    inference(ennf_transformation,[],[f11])).
% 1.58/1.00  
% 1.58/1.00  fof(f20,plain,(
% 1.58/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.58/1.00    inference(flattening,[],[f19])).
% 1.58/1.00  
% 1.58/1.00  fof(f24,plain,(
% 1.58/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & k1_relset_1(sK0,sK1,sK2) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f25,plain,(
% 1.58/1.00    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & k1_relset_1(sK0,sK1,sK2) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 1.58/1.00  
% 1.58/1.00  fof(f46,plain,(
% 1.58/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/1.00    inference(cnf_transformation,[],[f25])).
% 1.58/1.00  
% 1.58/1.00  fof(f8,axiom,(
% 1.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f15,plain,(
% 1.58/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/1.00    inference(ennf_transformation,[],[f8])).
% 1.58/1.00  
% 1.58/1.00  fof(f16,plain,(
% 1.58/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/1.00    inference(flattening,[],[f15])).
% 1.58/1.00  
% 1.58/1.00  fof(f23,plain,(
% 1.58/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/1.00    inference(nnf_transformation,[],[f16])).
% 1.58/1.00  
% 1.58/1.00  fof(f38,plain,(
% 1.58/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/1.00    inference(cnf_transformation,[],[f23])).
% 1.58/1.00  
% 1.58/1.00  fof(f48,plain,(
% 1.58/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.58/1.00    inference(cnf_transformation,[],[f25])).
% 1.58/1.00  
% 1.58/1.00  fof(f45,plain,(
% 1.58/1.00    v1_funct_1(sK2)),
% 1.58/1.00    inference(cnf_transformation,[],[f25])).
% 1.58/1.00  
% 1.58/1.00  fof(f47,plain,(
% 1.58/1.00    k1_relset_1(sK0,sK1,sK2) = sK0),
% 1.58/1.00    inference(cnf_transformation,[],[f25])).
% 1.58/1.00  
% 1.58/1.00  fof(f1,axiom,(
% 1.58/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f21,plain,(
% 1.58/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.58/1.00    inference(nnf_transformation,[],[f1])).
% 1.58/1.00  
% 1.58/1.00  fof(f22,plain,(
% 1.58/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.58/1.00    inference(flattening,[],[f21])).
% 1.58/1.00  
% 1.58/1.00  fof(f28,plain,(
% 1.58/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.58/1.00    inference(cnf_transformation,[],[f22])).
% 1.58/1.00  
% 1.58/1.00  fof(f49,plain,(
% 1.58/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.58/1.00    inference(equality_resolution,[],[f28])).
% 1.58/1.00  
% 1.58/1.00  fof(f5,axiom,(
% 1.58/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f12,plain,(
% 1.58/1.00    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f5])).
% 1.58/1.00  
% 1.58/1.00  fof(f33,plain,(
% 1.58/1.00    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.58/1.00    inference(cnf_transformation,[],[f12])).
% 1.58/1.00  
% 1.58/1.00  fof(f4,axiom,(
% 1.58/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f32,plain,(
% 1.58/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.58/1.00    inference(cnf_transformation,[],[f4])).
% 1.58/1.00  
% 1.58/1.00  fof(f2,axiom,(
% 1.58/1.00    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f29,plain,(
% 1.58/1.00    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f2])).
% 1.58/1.00  
% 1.58/1.00  fof(f41,plain,(
% 1.58/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/1.00    inference(cnf_transformation,[],[f23])).
% 1.58/1.00  
% 1.58/1.00  fof(f51,plain,(
% 1.58/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/1.00    inference(equality_resolution,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f52,plain,(
% 1.58/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.58/1.00    inference(equality_resolution,[],[f51])).
% 1.58/1.00  
% 1.58/1.00  fof(f3,axiom,(
% 1.58/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f30,plain,(
% 1.58/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.58/1.00    inference(cnf_transformation,[],[f3])).
% 1.58/1.00  
% 1.58/1.00  fof(f31,plain,(
% 1.58/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.58/1.00    inference(cnf_transformation,[],[f3])).
% 1.58/1.00  
% 1.58/1.00  fof(f26,plain,(
% 1.58/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 1.58/1.00    inference(cnf_transformation,[],[f22])).
% 1.58/1.00  
% 1.58/1.00  fof(f27,plain,(
% 1.58/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.58/1.00    inference(cnf_transformation,[],[f22])).
% 1.58/1.00  
% 1.58/1.00  fof(f50,plain,(
% 1.58/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 1.58/1.00    inference(equality_resolution,[],[f27])).
% 1.58/1.00  
% 1.58/1.00  fof(f6,axiom,(
% 1.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f13,plain,(
% 1.58/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/1.00    inference(ennf_transformation,[],[f6])).
% 1.58/1.00  
% 1.58/1.00  fof(f34,plain,(
% 1.58/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/1.00    inference(cnf_transformation,[],[f13])).
% 1.58/1.00  
% 1.58/1.00  fof(f9,axiom,(
% 1.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f17,plain,(
% 1.58/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f9])).
% 1.58/1.00  
% 1.58/1.00  fof(f18,plain,(
% 1.58/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/1.00    inference(flattening,[],[f17])).
% 1.58/1.00  
% 1.58/1.00  fof(f43,plain,(
% 1.58/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f18])).
% 1.58/1.00  
% 1.58/1.00  fof(f44,plain,(
% 1.58/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f18])).
% 1.58/1.00  
% 1.58/1.00  cnf(c_21,negated_conjecture,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.58/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_699,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_13,plain,
% 1.58/1.00      ( v1_funct_2(X0,X1,X2)
% 1.58/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.00      | k1_relset_1(X1,X2,X0) != X1
% 1.58/1.00      | k1_xboole_0 = X2 ),
% 1.58/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_19,negated_conjecture,
% 1.58/1.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 1.58/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.58/1.00      | ~ v1_funct_1(sK2) ),
% 1.58/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_22,negated_conjecture,
% 1.58/1.00      ( v1_funct_1(sK2) ),
% 1.58/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_96,negated_conjecture,
% 1.58/1.00      ( ~ v1_funct_2(sK2,sK0,sK1) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_19,c_22,c_21]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_323,plain,
% 1.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.00      | k1_relset_1(X1,X2,X0) != X1
% 1.58/1.00      | sK1 != X2
% 1.58/1.00      | sK0 != X1
% 1.58/1.00      | sK2 != X0
% 1.58/1.00      | k1_xboole_0 = X2 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_96]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_324,plain,
% 1.58/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.58/1.00      | k1_relset_1(sK0,sK1,sK2) != sK0
% 1.58/1.00      | k1_xboole_0 = sK1 ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_20,negated_conjecture,
% 1.58/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_326,plain,
% 1.58/1.00      ( k1_xboole_0 = sK1 ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_324,c_21,c_20]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_719,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 1.58/1.00      inference(light_normalisation,[status(thm)],[c_699,c_326]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_0,plain,
% 1.58/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_720,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.58/1.00      inference(demodulation,[status(thm)],[c_719,c_0]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_7,plain,
% 1.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.58/1.00      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_701,plain,
% 1.58/1.00      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 1.58/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1301,plain,
% 1.58/1.00      ( k9_relat_1(k6_relat_1(k1_xboole_0),sK2) = sK2 ),
% 1.58/1.00      inference(superposition,[status(thm)],[c_720,c_701]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_6,plain,
% 1.58/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1303,plain,
% 1.58/1.00      ( k9_relat_1(k1_xboole_0,sK2) = sK2 ),
% 1.58/1.00      inference(light_normalisation,[status(thm)],[c_1301,c_6]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_3,plain,
% 1.58/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1304,plain,
% 1.58/1.00      ( sK2 = k1_xboole_0 ),
% 1.58/1.00      inference(demodulation,[status(thm)],[c_1303,c_3]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_10,plain,
% 1.58/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 1.58/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.58/1.00      | k1_xboole_0 = X0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_247,plain,
% 1.58/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.58/1.00      | sK1 != k1_xboole_0
% 1.58/1.00      | sK0 != X0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_96]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_248,plain,
% 1.58/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 1.58/1.00      | sK1 != k1_xboole_0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = sK0 ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_247]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_697,plain,
% 1.58/1.00      ( sK1 != k1_xboole_0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = sK0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_766,plain,
% 1.58/1.00      ( sK0 = k1_xboole_0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != k1_xboole_0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.58/1.00      inference(light_normalisation,[status(thm)],[c_697,c_326]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_767,plain,
% 1.58/1.00      ( sK0 = k1_xboole_0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.58/1.00      inference(equality_resolution_simp,[status(thm)],[c_766]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_768,plain,
% 1.58/1.00      ( sK0 = k1_xboole_0
% 1.58/1.00      | sK2 != k1_xboole_0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.58/1.00      inference(demodulation,[status(thm)],[c_767,c_0]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_5,plain,
% 1.58/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_4,plain,
% 1.58/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_2,plain,
% 1.58/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = X1
% 1.58/1.00      | k1_xboole_0 = X0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f26]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_61,plain,
% 1.58/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1,plain,
% 1.58/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_62,plain,
% 1.58/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_8,plain,
% 1.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_17,plain,
% 1.58/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.58/1.00      | ~ v1_funct_1(X0)
% 1.58/1.00      | ~ v1_relat_1(X0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_183,plain,
% 1.58/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.58/1.00      | ~ v1_relat_1(X0)
% 1.58/1.00      | sK2 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_184,plain,
% 1.58/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_183]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_221,plain,
% 1.58/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 1.58/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.00      | sK2 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_184]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_222,plain,
% 1.58/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 1.58/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_221]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_352,plain,
% 1.58/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.00      | k1_relat_1(sK2) != sK0
% 1.58/1.00      | k2_relat_1(sK2) != sK1
% 1.58/1.00      | sK2 != sK2 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_96,c_222]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_409,plain,
% 1.58/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.00      | k1_relat_1(sK2) != sK0
% 1.58/1.00      | k2_relat_1(sK2) != sK1 ),
% 1.58/1.00      inference(equality_resolution_simp,[status(thm)],[c_352]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_477,plain,
% 1.58/1.00      ( sP0_iProver_split | k1_relat_1(sK2) != sK0 | k2_relat_1(sK2) != sK1 ),
% 1.58/1.00      inference(splitting,
% 1.58/1.00                [splitting(split),new_symbols(definition,[])],
% 1.58/1.00                [c_409]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_688,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != sK0
% 1.58/1.00      | k2_relat_1(sK2) != sK1
% 1.58/1.00      | sP0_iProver_split = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_737,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != sK0
% 1.58/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 1.58/1.00      | sP0_iProver_split = iProver_top ),
% 1.58/1.00      inference(light_normalisation,[status(thm)],[c_688,c_326]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_835,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != X0 | k1_relat_1(sK2) = sK0 | sK0 != X0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_836,plain,
% 1.58/1.00      ( k1_relat_1(sK2) = sK0
% 1.58/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 1.58/1.00      | sK0 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_16,plain,
% 1.58/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.58/1.00      | ~ v1_funct_1(X0)
% 1.58/1.00      | ~ v1_relat_1(X0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_193,plain,
% 1.58/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.58/1.00      | ~ v1_relat_1(X0)
% 1.58/1.00      | sK2 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_194,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 1.58/1.00      | ~ v1_relat_1(sK2) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_193]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_209,plain,
% 1.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 1.58/1.00      | sK2 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_194]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_210,plain,
% 1.58/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_209]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_698,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.58/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_24,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_817,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 1.58/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_210]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_818,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 1.58/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_849,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_698,c_24,c_818]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_476,plain,
% 1.58/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.00      | ~ sP0_iProver_split ),
% 1.58/1.00      inference(splitting,
% 1.58/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.58/1.00                [c_409]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_689,plain,
% 1.58/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.58/1.00      | sP0_iProver_split != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_854,plain,
% 1.58/1.00      ( sP0_iProver_split != iProver_top ),
% 1.58/1.00      inference(superposition,[status(thm)],[c_849,c_689]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_832,plain,
% 1.58/1.00      ( k2_relat_1(sK2) != X0
% 1.58/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != X0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_896,plain,
% 1.58/1.00      ( k2_relat_1(sK2) != k2_relat_1(X0)
% 1.58/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != k2_relat_1(X0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_832]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_898,plain,
% 1.58/1.00      ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
% 1.58/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_896]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_486,plain,
% 1.58/1.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 1.58/1.00      theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_897,plain,
% 1.58/1.00      ( k2_relat_1(sK2) = k2_relat_1(X0) | sK2 != X0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_486]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_899,plain,
% 1.58/1.00      ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_897]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_834,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != X0
% 1.58/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != X0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_903,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 1.58/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != k1_relat_1(X0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_834]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_905,plain,
% 1.58/1.00      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 1.58/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 1.58/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_903]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_487,plain,
% 1.58/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 1.58/1.00      theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_904,plain,
% 1.58/1.00      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_487]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_906,plain,
% 1.58/1.00      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_904]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1030,plain,
% 1.58/1.00      ( k2_relat_1(X0) != X1
% 1.58/1.00      | k1_xboole_0 != X1
% 1.58/1.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1031,plain,
% 1.58/1.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 1.58/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1030]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1038,plain,
% 1.58/1.00      ( k1_relat_1(X0) != X1
% 1.58/1.00      | k1_xboole_0 != X1
% 1.58/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1039,plain,
% 1.58/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 1.58/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1038]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1097,plain,
% 1.58/1.00      ( sK2 != k1_xboole_0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_768,c_5,c_4,c_61,c_62,c_737,c_836,c_854,c_898,c_899,
% 1.58/1.00                 c_905,c_906,c_1031,c_1039]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1313,plain,
% 1.58/1.00      ( k1_xboole_0 != k1_xboole_0
% 1.58/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.58/1.00      inference(demodulation,[status(thm)],[c_1304,c_1097]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1346,plain,
% 1.58/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.58/1.00      inference(equality_resolution_simp,[status(thm)],[c_1313]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1318,plain,
% 1.58/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.58/1.00      inference(demodulation,[status(thm)],[c_1304,c_720]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1348,plain,
% 1.58/1.00      ( $false ),
% 1.58/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1346,c_1318]) ).
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  ------                               Statistics
% 1.58/1.00  
% 1.58/1.00  ------ General
% 1.58/1.00  
% 1.58/1.00  abstr_ref_over_cycles:                  0
% 1.58/1.00  abstr_ref_under_cycles:                 0
% 1.58/1.00  gc_basic_clause_elim:                   0
% 1.58/1.00  forced_gc_time:                         0
% 1.58/1.00  parsing_time:                           0.006
% 1.58/1.00  unif_index_cands_time:                  0.
% 1.58/1.00  unif_index_add_time:                    0.
% 1.58/1.00  orderings_time:                         0.
% 1.58/1.00  out_proof_time:                         0.008
% 1.58/1.00  total_time:                             0.058
% 1.58/1.00  num_of_symbols:                         47
% 1.58/1.00  num_of_terms:                           1128
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing
% 1.58/1.00  
% 1.58/1.00  num_of_splits:                          4
% 1.58/1.00  num_of_split_atoms:                     1
% 1.58/1.00  num_of_reused_defs:                     3
% 1.58/1.00  num_eq_ax_congr_red:                    4
% 1.58/1.00  num_of_sem_filtered_clauses:            1
% 1.58/1.00  num_of_subtypes:                        0
% 1.58/1.00  monotx_restored_types:                  0
% 1.58/1.00  sat_num_of_epr_types:                   0
% 1.58/1.00  sat_num_of_non_cyclic_types:            0
% 1.58/1.00  sat_guarded_non_collapsed_types:        0
% 1.58/1.00  num_pure_diseq_elim:                    0
% 1.58/1.00  simp_replaced_by:                       0
% 1.58/1.00  res_preprocessed:                       102
% 1.58/1.00  prep_upred:                             0
% 1.58/1.00  prep_unflattend:                        37
% 1.58/1.00  smt_new_axioms:                         0
% 1.58/1.00  pred_elim_cands:                        1
% 1.58/1.00  pred_elim:                              3
% 1.58/1.00  pred_elim_cl:                           3
% 1.58/1.00  pred_elim_cycles:                       5
% 1.58/1.00  merged_defs:                            0
% 1.58/1.00  merged_defs_ncl:                        0
% 1.58/1.00  bin_hyper_res:                          0
% 1.58/1.00  prep_cycles:                            4
% 1.58/1.00  pred_elim_time:                         0.003
% 1.58/1.00  splitting_time:                         0.
% 1.58/1.00  sem_filter_time:                        0.
% 1.58/1.00  monotx_time:                            0.
% 1.58/1.00  subtype_inf_time:                       0.
% 1.58/1.00  
% 1.58/1.00  ------ Problem properties
% 1.58/1.00  
% 1.58/1.00  clauses:                                23
% 1.58/1.00  conjectures:                            2
% 1.58/1.00  epr:                                    1
% 1.58/1.00  horn:                                   19
% 1.58/1.00  ground:                                 12
% 1.58/1.00  unary:                                  9
% 1.58/1.00  binary:                                 7
% 1.58/1.00  lits:                                   48
% 1.58/1.00  lits_eq:                                27
% 1.58/1.00  fd_pure:                                0
% 1.58/1.00  fd_pseudo:                              0
% 1.58/1.00  fd_cond:                                1
% 1.58/1.00  fd_pseudo_cond:                         0
% 1.58/1.00  ac_symbols:                             0
% 1.58/1.00  
% 1.58/1.00  ------ Propositional Solver
% 1.58/1.00  
% 1.58/1.00  prop_solver_calls:                      26
% 1.58/1.00  prop_fast_solver_calls:                 533
% 1.58/1.00  smt_solver_calls:                       0
% 1.58/1.00  smt_fast_solver_calls:                  0
% 1.58/1.00  prop_num_of_clauses:                    396
% 1.58/1.00  prop_preprocess_simplified:             2375
% 1.58/1.00  prop_fo_subsumed:                       12
% 1.58/1.00  prop_solver_time:                       0.
% 1.58/1.00  smt_solver_time:                        0.
% 1.58/1.00  smt_fast_solver_time:                   0.
% 1.58/1.00  prop_fast_solver_time:                  0.
% 1.58/1.00  prop_unsat_core_time:                   0.
% 1.58/1.00  
% 1.58/1.00  ------ QBF
% 1.58/1.00  
% 1.58/1.00  qbf_q_res:                              0
% 1.58/1.00  qbf_num_tautologies:                    0
% 1.58/1.00  qbf_prep_cycles:                        0
% 1.58/1.00  
% 1.58/1.00  ------ BMC1
% 1.58/1.00  
% 1.58/1.00  bmc1_current_bound:                     -1
% 1.58/1.00  bmc1_last_solved_bound:                 -1
% 1.58/1.00  bmc1_unsat_core_size:                   -1
% 1.58/1.00  bmc1_unsat_core_parents_size:           -1
% 1.58/1.00  bmc1_merge_next_fun:                    0
% 1.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation
% 1.58/1.00  
% 1.58/1.00  inst_num_of_clauses:                    154
% 1.58/1.00  inst_num_in_passive:                    40
% 1.58/1.00  inst_num_in_active:                     92
% 1.58/1.00  inst_num_in_unprocessed:                22
% 1.58/1.00  inst_num_of_loops:                      100
% 1.58/1.00  inst_num_of_learning_restarts:          0
% 1.58/1.00  inst_num_moves_active_passive:          6
% 1.58/1.00  inst_lit_activity:                      0
% 1.58/1.00  inst_lit_activity_moves:                0
% 1.58/1.00  inst_num_tautologies:                   0
% 1.58/1.00  inst_num_prop_implied:                  0
% 1.58/1.00  inst_num_existing_simplified:           0
% 1.58/1.00  inst_num_eq_res_simplified:             0
% 1.58/1.00  inst_num_child_elim:                    0
% 1.58/1.00  inst_num_of_dismatching_blockings:      8
% 1.58/1.00  inst_num_of_non_proper_insts:           111
% 1.58/1.00  inst_num_of_duplicates:                 0
% 1.58/1.00  inst_inst_num_from_inst_to_res:         0
% 1.58/1.00  inst_dismatching_checking_time:         0.
% 1.58/1.00  
% 1.58/1.00  ------ Resolution
% 1.58/1.00  
% 1.58/1.00  res_num_of_clauses:                     0
% 1.58/1.00  res_num_in_passive:                     0
% 1.58/1.00  res_num_in_active:                      0
% 1.58/1.00  res_num_of_loops:                       106
% 1.58/1.00  res_forward_subset_subsumed:            7
% 1.58/1.00  res_backward_subset_subsumed:           0
% 1.58/1.00  res_forward_subsumed:                   0
% 1.58/1.00  res_backward_subsumed:                  0
% 1.58/1.00  res_forward_subsumption_resolution:     0
% 1.58/1.00  res_backward_subsumption_resolution:    0
% 1.58/1.00  res_clause_to_clause_subsumption:       42
% 1.58/1.00  res_orphan_elimination:                 0
% 1.58/1.00  res_tautology_del:                      21
% 1.58/1.00  res_num_eq_res_simplified:              1
% 1.58/1.00  res_num_sel_changes:                    0
% 1.58/1.00  res_moves_from_active_to_pass:          0
% 1.58/1.00  
% 1.58/1.00  ------ Superposition
% 1.58/1.00  
% 1.58/1.00  sup_time_total:                         0.
% 1.58/1.00  sup_time_generating:                    0.
% 1.58/1.00  sup_time_sim_full:                      0.
% 1.58/1.00  sup_time_sim_immed:                     0.
% 1.58/1.00  
% 1.58/1.00  sup_num_of_clauses:                     12
% 1.58/1.00  sup_num_in_active:                      9
% 1.58/1.00  sup_num_in_passive:                     3
% 1.58/1.00  sup_num_of_loops:                       19
% 1.58/1.00  sup_fw_superposition:                   2
% 1.58/1.00  sup_bw_superposition:                   3
% 1.58/1.00  sup_immediate_simplified:               4
% 1.58/1.00  sup_given_eliminated:                   0
% 1.58/1.00  comparisons_done:                       0
% 1.58/1.00  comparisons_avoided:                    0
% 1.58/1.00  
% 1.58/1.00  ------ Simplifications
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  sim_fw_subset_subsumed:                 2
% 1.58/1.00  sim_bw_subset_subsumed:                 1
% 1.58/1.00  sim_fw_subsumed:                        0
% 1.58/1.00  sim_bw_subsumed:                        0
% 1.58/1.00  sim_fw_subsumption_res:                 4
% 1.58/1.00  sim_bw_subsumption_res:                 0
% 1.58/1.00  sim_tautology_del:                      0
% 1.58/1.00  sim_eq_tautology_del:                   1
% 1.58/1.00  sim_eq_res_simp:                        4
% 1.58/1.00  sim_fw_demodulated:                     8
% 1.58/1.00  sim_bw_demodulated:                     11
% 1.58/1.00  sim_light_normalised:                   11
% 1.58/1.00  sim_joinable_taut:                      0
% 1.58/1.00  sim_joinable_simp:                      0
% 1.58/1.00  sim_ac_normalised:                      0
% 1.58/1.00  sim_smt_subsumption:                    0
% 1.58/1.00  
%------------------------------------------------------------------------------
