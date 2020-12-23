%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:20 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 735 expanded)
%              Number of clauses        :   43 ( 188 expanded)
%              Number of leaves         :    8 ( 152 expanded)
%              Depth                    :   20
%              Number of atoms          :  232 (3659 expanded)
%              Number of equality atoms :  140 (1126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,
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

fof(f46,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & k1_relset_1(sK0,sK1,sK2) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f88,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1759,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_162,negated_conjecture,
    ( ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_37,c_36])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK1 != X2
    | sK0 != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_162])).

cnf(c_438,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) != sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_35,negated_conjecture,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_440,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_36,c_35])).

cnf(c_1808,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1759,c_440])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1809,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1808,c_4])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1761,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3239,plain,
    ( k9_relat_1(k6_relat_1(k1_xboole_0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1809,c_1761])).

cnf(c_20,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3241,plain,
    ( k9_relat_1(k1_xboole_0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3239,c_20])).

cnf(c_12,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3242,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3241,c_12])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_162])).

cnf(c_404,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1755,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1869,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1755,c_440])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1870,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1869,c_5])).

cnf(c_1874,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1870,c_1809])).

cnf(c_3260,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3242,c_1874])).

cnf(c_25,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_356,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_162])).

cnf(c_357,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_367,plain,
    ( sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_357,c_7])).

cnf(c_1825,plain,
    ( sK0 = k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_367,c_440])).

cnf(c_1826,plain,
    ( sK0 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1825])).

cnf(c_3261,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3242,c_1826])).

cnf(c_3284,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3261])).

cnf(c_1799,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_35,c_440])).

cnf(c_3265,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_3242,c_1799])).

cnf(c_3287,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3284,c_3265])).

cnf(c_3296,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3260,c_3284,c_3287])).

cnf(c_3297,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3296])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.11/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/0.98  
% 2.11/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/0.98  
% 2.11/0.98  ------  iProver source info
% 2.11/0.98  
% 2.11/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.11/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/0.98  git: non_committed_changes: false
% 2.11/0.98  git: last_make_outside_of_git: false
% 2.11/0.98  
% 2.11/0.98  ------ 
% 2.11/0.98  
% 2.11/0.98  ------ Input Options
% 2.11/0.98  
% 2.11/0.98  --out_options                           all
% 2.11/0.98  --tptp_safe_out                         true
% 2.11/0.98  --problem_path                          ""
% 2.11/0.98  --include_path                          ""
% 2.11/0.98  --clausifier                            res/vclausify_rel
% 2.11/0.98  --clausifier_options                    --mode clausify
% 2.11/0.98  --stdin                                 false
% 2.11/0.98  --stats_out                             all
% 2.11/0.98  
% 2.11/0.98  ------ General Options
% 2.11/0.98  
% 2.11/0.98  --fof                                   false
% 2.11/0.98  --time_out_real                         305.
% 2.11/0.98  --time_out_virtual                      -1.
% 2.11/0.98  --symbol_type_check                     false
% 2.11/0.98  --clausify_out                          false
% 2.11/0.98  --sig_cnt_out                           false
% 2.11/0.98  --trig_cnt_out                          false
% 2.11/0.98  --trig_cnt_out_tolerance                1.
% 2.11/0.98  --trig_cnt_out_sk_spl                   false
% 2.11/0.98  --abstr_cl_out                          false
% 2.11/0.98  
% 2.11/0.98  ------ Global Options
% 2.11/0.98  
% 2.11/0.98  --schedule                              default
% 2.11/0.98  --add_important_lit                     false
% 2.11/0.98  --prop_solver_per_cl                    1000
% 2.11/0.98  --min_unsat_core                        false
% 2.11/0.98  --soft_assumptions                      false
% 2.11/0.98  --soft_lemma_size                       3
% 2.11/0.98  --prop_impl_unit_size                   0
% 2.11/0.98  --prop_impl_unit                        []
% 2.11/0.98  --share_sel_clauses                     true
% 2.11/0.98  --reset_solvers                         false
% 2.11/0.98  --bc_imp_inh                            [conj_cone]
% 2.11/0.98  --conj_cone_tolerance                   3.
% 2.11/0.98  --extra_neg_conj                        none
% 2.11/0.98  --large_theory_mode                     true
% 2.11/0.98  --prolific_symb_bound                   200
% 2.11/0.98  --lt_threshold                          2000
% 2.11/0.98  --clause_weak_htbl                      true
% 2.11/0.98  --gc_record_bc_elim                     false
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing Options
% 2.11/0.98  
% 2.11/0.98  --preprocessing_flag                    true
% 2.11/0.98  --time_out_prep_mult                    0.1
% 2.11/0.98  --splitting_mode                        input
% 2.11/0.98  --splitting_grd                         true
% 2.11/0.98  --splitting_cvd                         false
% 2.11/0.98  --splitting_cvd_svl                     false
% 2.11/0.98  --splitting_nvd                         32
% 2.11/0.98  --sub_typing                            true
% 2.11/0.98  --prep_gs_sim                           true
% 2.11/0.98  --prep_unflatten                        true
% 2.11/0.98  --prep_res_sim                          true
% 2.11/0.98  --prep_upred                            true
% 2.11/0.98  --prep_sem_filter                       exhaustive
% 2.11/0.98  --prep_sem_filter_out                   false
% 2.11/0.98  --pred_elim                             true
% 2.11/0.98  --res_sim_input                         true
% 2.11/0.98  --eq_ax_congr_red                       true
% 2.11/0.98  --pure_diseq_elim                       true
% 2.11/0.98  --brand_transform                       false
% 2.11/0.98  --non_eq_to_eq                          false
% 2.11/0.98  --prep_def_merge                        true
% 2.11/0.98  --prep_def_merge_prop_impl              false
% 2.11/0.98  --prep_def_merge_mbd                    true
% 2.11/0.98  --prep_def_merge_tr_red                 false
% 2.11/0.98  --prep_def_merge_tr_cl                  false
% 2.11/0.98  --smt_preprocessing                     true
% 2.11/0.98  --smt_ac_axioms                         fast
% 2.11/0.98  --preprocessed_out                      false
% 2.11/0.98  --preprocessed_stats                    false
% 2.11/0.98  
% 2.11/0.98  ------ Abstraction refinement Options
% 2.11/0.98  
% 2.11/0.98  --abstr_ref                             []
% 2.11/0.98  --abstr_ref_prep                        false
% 2.11/0.98  --abstr_ref_until_sat                   false
% 2.11/0.98  --abstr_ref_sig_restrict                funpre
% 2.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.98  --abstr_ref_under                       []
% 2.11/0.98  
% 2.11/0.98  ------ SAT Options
% 2.11/0.98  
% 2.11/0.98  --sat_mode                              false
% 2.11/0.98  --sat_fm_restart_options                ""
% 2.11/0.98  --sat_gr_def                            false
% 2.11/0.98  --sat_epr_types                         true
% 2.11/0.98  --sat_non_cyclic_types                  false
% 2.11/0.98  --sat_finite_models                     false
% 2.11/0.98  --sat_fm_lemmas                         false
% 2.11/0.98  --sat_fm_prep                           false
% 2.11/0.98  --sat_fm_uc_incr                        true
% 2.11/0.98  --sat_out_model                         small
% 2.11/0.98  --sat_out_clauses                       false
% 2.11/0.98  
% 2.11/0.98  ------ QBF Options
% 2.11/0.98  
% 2.11/0.98  --qbf_mode                              false
% 2.11/0.98  --qbf_elim_univ                         false
% 2.11/0.98  --qbf_dom_inst                          none
% 2.11/0.98  --qbf_dom_pre_inst                      false
% 2.11/0.98  --qbf_sk_in                             false
% 2.11/0.98  --qbf_pred_elim                         true
% 2.11/0.98  --qbf_split                             512
% 2.11/0.98  
% 2.11/0.98  ------ BMC1 Options
% 2.11/0.98  
% 2.11/0.98  --bmc1_incremental                      false
% 2.11/0.98  --bmc1_axioms                           reachable_all
% 2.11/0.98  --bmc1_min_bound                        0
% 2.11/0.98  --bmc1_max_bound                        -1
% 2.11/0.98  --bmc1_max_bound_default                -1
% 2.11/0.98  --bmc1_symbol_reachability              true
% 2.11/0.98  --bmc1_property_lemmas                  false
% 2.11/0.98  --bmc1_k_induction                      false
% 2.11/0.98  --bmc1_non_equiv_states                 false
% 2.11/0.98  --bmc1_deadlock                         false
% 2.11/0.98  --bmc1_ucm                              false
% 2.11/0.98  --bmc1_add_unsat_core                   none
% 2.11/0.98  --bmc1_unsat_core_children              false
% 2.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.98  --bmc1_out_stat                         full
% 2.11/0.98  --bmc1_ground_init                      false
% 2.11/0.98  --bmc1_pre_inst_next_state              false
% 2.11/0.98  --bmc1_pre_inst_state                   false
% 2.11/0.98  --bmc1_pre_inst_reach_state             false
% 2.11/0.98  --bmc1_out_unsat_core                   false
% 2.11/0.98  --bmc1_aig_witness_out                  false
% 2.11/0.98  --bmc1_verbose                          false
% 2.11/0.98  --bmc1_dump_clauses_tptp                false
% 2.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.98  --bmc1_dump_file                        -
% 2.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.98  --bmc1_ucm_extend_mode                  1
% 2.11/0.98  --bmc1_ucm_init_mode                    2
% 2.11/0.98  --bmc1_ucm_cone_mode                    none
% 2.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.98  --bmc1_ucm_relax_model                  4
% 2.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.98  --bmc1_ucm_layered_model                none
% 2.11/0.98  --bmc1_ucm_max_lemma_size               10
% 2.11/0.98  
% 2.11/0.98  ------ AIG Options
% 2.11/0.98  
% 2.11/0.98  --aig_mode                              false
% 2.11/0.98  
% 2.11/0.98  ------ Instantiation Options
% 2.11/0.98  
% 2.11/0.98  --instantiation_flag                    true
% 2.11/0.98  --inst_sos_flag                         false
% 2.11/0.98  --inst_sos_phase                        true
% 2.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.98  --inst_lit_sel_side                     num_symb
% 2.11/0.98  --inst_solver_per_active                1400
% 2.11/0.98  --inst_solver_calls_frac                1.
% 2.11/0.98  --inst_passive_queue_type               priority_queues
% 2.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.98  --inst_passive_queues_freq              [25;2]
% 2.11/0.98  --inst_dismatching                      true
% 2.11/0.98  --inst_eager_unprocessed_to_passive     true
% 2.11/0.98  --inst_prop_sim_given                   true
% 2.11/0.98  --inst_prop_sim_new                     false
% 2.11/0.98  --inst_subs_new                         false
% 2.11/0.98  --inst_eq_res_simp                      false
% 2.11/0.98  --inst_subs_given                       false
% 2.11/0.98  --inst_orphan_elimination               true
% 2.11/0.98  --inst_learning_loop_flag               true
% 2.11/0.98  --inst_learning_start                   3000
% 2.11/0.98  --inst_learning_factor                  2
% 2.11/0.98  --inst_start_prop_sim_after_learn       3
% 2.11/0.98  --inst_sel_renew                        solver
% 2.11/0.98  --inst_lit_activity_flag                true
% 2.11/0.98  --inst_restr_to_given                   false
% 2.11/0.98  --inst_activity_threshold               500
% 2.11/0.98  --inst_out_proof                        true
% 2.11/0.98  
% 2.11/0.98  ------ Resolution Options
% 2.11/0.98  
% 2.11/0.98  --resolution_flag                       true
% 2.11/0.98  --res_lit_sel                           adaptive
% 2.11/0.98  --res_lit_sel_side                      none
% 2.11/0.98  --res_ordering                          kbo
% 2.11/0.98  --res_to_prop_solver                    active
% 2.11/0.98  --res_prop_simpl_new                    false
% 2.11/0.98  --res_prop_simpl_given                  true
% 2.11/0.98  --res_passive_queue_type                priority_queues
% 2.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.98  --res_passive_queues_freq               [15;5]
% 2.11/0.98  --res_forward_subs                      full
% 2.11/0.98  --res_backward_subs                     full
% 2.11/0.98  --res_forward_subs_resolution           true
% 2.11/0.98  --res_backward_subs_resolution          true
% 2.11/0.98  --res_orphan_elimination                true
% 2.11/0.98  --res_time_limit                        2.
% 2.11/0.98  --res_out_proof                         true
% 2.11/0.98  
% 2.11/0.98  ------ Superposition Options
% 2.11/0.98  
% 2.11/0.98  --superposition_flag                    true
% 2.11/0.98  --sup_passive_queue_type                priority_queues
% 2.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.98  --demod_completeness_check              fast
% 2.11/0.98  --demod_use_ground                      true
% 2.11/0.98  --sup_to_prop_solver                    passive
% 2.11/0.98  --sup_prop_simpl_new                    true
% 2.11/0.98  --sup_prop_simpl_given                  true
% 2.11/0.98  --sup_fun_splitting                     false
% 2.11/0.98  --sup_smt_interval                      50000
% 2.11/0.98  
% 2.11/0.98  ------ Superposition Simplification Setup
% 2.11/0.98  
% 2.11/0.98  --sup_indices_passive                   []
% 2.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_full_bw                           [BwDemod]
% 2.11/0.98  --sup_immed_triv                        [TrivRules]
% 2.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_immed_bw_main                     []
% 2.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.98  
% 2.11/0.98  ------ Combination Options
% 2.11/0.98  
% 2.11/0.98  --comb_res_mult                         3
% 2.11/0.98  --comb_sup_mult                         2
% 2.11/0.98  --comb_inst_mult                        10
% 2.11/0.98  
% 2.11/0.98  ------ Debug Options
% 2.11/0.98  
% 2.11/0.98  --dbg_backtrace                         false
% 2.11/0.98  --dbg_dump_prop_clauses                 false
% 2.11/0.98  --dbg_dump_prop_clauses_file            -
% 2.11/0.98  --dbg_out_stat                          false
% 2.11/0.98  ------ Parsing...
% 2.11/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/0.98  ------ Proving...
% 2.11/0.98  ------ Problem Properties 
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  clauses                                 36
% 2.11/0.98  conjectures                             3
% 2.11/0.98  EPR                                     4
% 2.11/0.98  Horn                                    33
% 2.11/0.98  unary                                   18
% 2.11/0.98  binary                                  5
% 2.11/0.98  lits                                    74
% 2.11/0.98  lits eq                                 34
% 2.11/0.98  fd_pure                                 0
% 2.11/0.98  fd_pseudo                               0
% 2.11/0.98  fd_cond                                 2
% 2.11/0.98  fd_pseudo_cond                          0
% 2.11/0.98  AC symbols                              0
% 2.11/0.98  
% 2.11/0.98  ------ Schedule dynamic 5 is on 
% 2.11/0.98  
% 2.11/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  ------ 
% 2.11/0.98  Current options:
% 2.11/0.98  ------ 
% 2.11/0.98  
% 2.11/0.98  ------ Input Options
% 2.11/0.98  
% 2.11/0.98  --out_options                           all
% 2.11/0.98  --tptp_safe_out                         true
% 2.11/0.98  --problem_path                          ""
% 2.11/0.98  --include_path                          ""
% 2.11/0.98  --clausifier                            res/vclausify_rel
% 2.11/0.98  --clausifier_options                    --mode clausify
% 2.11/0.98  --stdin                                 false
% 2.11/0.98  --stats_out                             all
% 2.11/0.98  
% 2.11/0.98  ------ General Options
% 2.11/0.98  
% 2.11/0.98  --fof                                   false
% 2.11/0.98  --time_out_real                         305.
% 2.11/0.98  --time_out_virtual                      -1.
% 2.11/0.98  --symbol_type_check                     false
% 2.11/0.98  --clausify_out                          false
% 2.11/0.98  --sig_cnt_out                           false
% 2.11/0.98  --trig_cnt_out                          false
% 2.11/0.98  --trig_cnt_out_tolerance                1.
% 2.11/0.98  --trig_cnt_out_sk_spl                   false
% 2.11/0.98  --abstr_cl_out                          false
% 2.11/0.98  
% 2.11/0.98  ------ Global Options
% 2.11/0.98  
% 2.11/0.98  --schedule                              default
% 2.11/0.98  --add_important_lit                     false
% 2.11/0.98  --prop_solver_per_cl                    1000
% 2.11/0.98  --min_unsat_core                        false
% 2.11/0.98  --soft_assumptions                      false
% 2.11/0.98  --soft_lemma_size                       3
% 2.11/0.98  --prop_impl_unit_size                   0
% 2.11/0.98  --prop_impl_unit                        []
% 2.11/0.98  --share_sel_clauses                     true
% 2.11/0.98  --reset_solvers                         false
% 2.11/0.98  --bc_imp_inh                            [conj_cone]
% 2.11/0.98  --conj_cone_tolerance                   3.
% 2.11/0.98  --extra_neg_conj                        none
% 2.11/0.98  --large_theory_mode                     true
% 2.11/0.98  --prolific_symb_bound                   200
% 2.11/0.98  --lt_threshold                          2000
% 2.11/0.98  --clause_weak_htbl                      true
% 2.11/0.98  --gc_record_bc_elim                     false
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing Options
% 2.11/0.98  
% 2.11/0.98  --preprocessing_flag                    true
% 2.11/0.98  --time_out_prep_mult                    0.1
% 2.11/0.98  --splitting_mode                        input
% 2.11/0.98  --splitting_grd                         true
% 2.11/0.98  --splitting_cvd                         false
% 2.11/0.98  --splitting_cvd_svl                     false
% 2.11/0.98  --splitting_nvd                         32
% 2.11/0.98  --sub_typing                            true
% 2.11/0.98  --prep_gs_sim                           true
% 2.11/0.98  --prep_unflatten                        true
% 2.11/0.98  --prep_res_sim                          true
% 2.11/0.98  --prep_upred                            true
% 2.11/0.98  --prep_sem_filter                       exhaustive
% 2.11/0.98  --prep_sem_filter_out                   false
% 2.11/0.98  --pred_elim                             true
% 2.11/0.98  --res_sim_input                         true
% 2.11/0.98  --eq_ax_congr_red                       true
% 2.11/0.98  --pure_diseq_elim                       true
% 2.11/0.98  --brand_transform                       false
% 2.11/0.98  --non_eq_to_eq                          false
% 2.11/0.98  --prep_def_merge                        true
% 2.11/0.98  --prep_def_merge_prop_impl              false
% 2.11/0.98  --prep_def_merge_mbd                    true
% 2.11/0.98  --prep_def_merge_tr_red                 false
% 2.11/0.98  --prep_def_merge_tr_cl                  false
% 2.11/0.98  --smt_preprocessing                     true
% 2.11/0.98  --smt_ac_axioms                         fast
% 2.11/0.98  --preprocessed_out                      false
% 2.11/0.98  --preprocessed_stats                    false
% 2.11/0.98  
% 2.11/0.98  ------ Abstraction refinement Options
% 2.11/0.98  
% 2.11/0.98  --abstr_ref                             []
% 2.11/0.98  --abstr_ref_prep                        false
% 2.11/0.98  --abstr_ref_until_sat                   false
% 2.11/0.98  --abstr_ref_sig_restrict                funpre
% 2.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.98  --abstr_ref_under                       []
% 2.11/0.98  
% 2.11/0.98  ------ SAT Options
% 2.11/0.98  
% 2.11/0.98  --sat_mode                              false
% 2.11/0.98  --sat_fm_restart_options                ""
% 2.11/0.98  --sat_gr_def                            false
% 2.11/0.98  --sat_epr_types                         true
% 2.11/0.98  --sat_non_cyclic_types                  false
% 2.11/0.98  --sat_finite_models                     false
% 2.11/0.98  --sat_fm_lemmas                         false
% 2.11/0.98  --sat_fm_prep                           false
% 2.11/0.98  --sat_fm_uc_incr                        true
% 2.11/0.98  --sat_out_model                         small
% 2.11/0.98  --sat_out_clauses                       false
% 2.11/0.98  
% 2.11/0.98  ------ QBF Options
% 2.11/0.98  
% 2.11/0.98  --qbf_mode                              false
% 2.11/0.98  --qbf_elim_univ                         false
% 2.11/0.98  --qbf_dom_inst                          none
% 2.11/0.98  --qbf_dom_pre_inst                      false
% 2.11/0.98  --qbf_sk_in                             false
% 2.11/0.98  --qbf_pred_elim                         true
% 2.11/0.98  --qbf_split                             512
% 2.11/0.98  
% 2.11/0.98  ------ BMC1 Options
% 2.11/0.98  
% 2.11/0.98  --bmc1_incremental                      false
% 2.11/0.98  --bmc1_axioms                           reachable_all
% 2.11/0.98  --bmc1_min_bound                        0
% 2.11/0.98  --bmc1_max_bound                        -1
% 2.11/0.98  --bmc1_max_bound_default                -1
% 2.11/0.98  --bmc1_symbol_reachability              true
% 2.11/0.98  --bmc1_property_lemmas                  false
% 2.11/0.98  --bmc1_k_induction                      false
% 2.11/0.98  --bmc1_non_equiv_states                 false
% 2.11/0.98  --bmc1_deadlock                         false
% 2.11/0.98  --bmc1_ucm                              false
% 2.11/0.98  --bmc1_add_unsat_core                   none
% 2.11/0.98  --bmc1_unsat_core_children              false
% 2.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.98  --bmc1_out_stat                         full
% 2.11/0.98  --bmc1_ground_init                      false
% 2.11/0.98  --bmc1_pre_inst_next_state              false
% 2.11/0.98  --bmc1_pre_inst_state                   false
% 2.11/0.98  --bmc1_pre_inst_reach_state             false
% 2.11/0.98  --bmc1_out_unsat_core                   false
% 2.11/0.98  --bmc1_aig_witness_out                  false
% 2.11/0.98  --bmc1_verbose                          false
% 2.11/0.98  --bmc1_dump_clauses_tptp                false
% 2.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.98  --bmc1_dump_file                        -
% 2.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.98  --bmc1_ucm_extend_mode                  1
% 2.11/0.98  --bmc1_ucm_init_mode                    2
% 2.11/0.98  --bmc1_ucm_cone_mode                    none
% 2.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.98  --bmc1_ucm_relax_model                  4
% 2.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.98  --bmc1_ucm_layered_model                none
% 2.11/0.98  --bmc1_ucm_max_lemma_size               10
% 2.11/0.98  
% 2.11/0.98  ------ AIG Options
% 2.11/0.98  
% 2.11/0.98  --aig_mode                              false
% 2.11/0.98  
% 2.11/0.98  ------ Instantiation Options
% 2.11/0.98  
% 2.11/0.98  --instantiation_flag                    true
% 2.11/0.98  --inst_sos_flag                         false
% 2.11/0.98  --inst_sos_phase                        true
% 2.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.98  --inst_lit_sel_side                     none
% 2.11/0.98  --inst_solver_per_active                1400
% 2.11/0.98  --inst_solver_calls_frac                1.
% 2.11/0.98  --inst_passive_queue_type               priority_queues
% 2.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.98  --inst_passive_queues_freq              [25;2]
% 2.11/0.98  --inst_dismatching                      true
% 2.11/0.98  --inst_eager_unprocessed_to_passive     true
% 2.11/0.98  --inst_prop_sim_given                   true
% 2.11/0.98  --inst_prop_sim_new                     false
% 2.11/0.98  --inst_subs_new                         false
% 2.11/0.98  --inst_eq_res_simp                      false
% 2.11/0.98  --inst_subs_given                       false
% 2.11/0.98  --inst_orphan_elimination               true
% 2.11/0.98  --inst_learning_loop_flag               true
% 2.11/0.98  --inst_learning_start                   3000
% 2.11/0.98  --inst_learning_factor                  2
% 2.11/0.98  --inst_start_prop_sim_after_learn       3
% 2.11/0.98  --inst_sel_renew                        solver
% 2.11/0.98  --inst_lit_activity_flag                true
% 2.11/0.98  --inst_restr_to_given                   false
% 2.11/0.98  --inst_activity_threshold               500
% 2.11/0.98  --inst_out_proof                        true
% 2.11/0.98  
% 2.11/0.98  ------ Resolution Options
% 2.11/0.98  
% 2.11/0.98  --resolution_flag                       false
% 2.11/0.98  --res_lit_sel                           adaptive
% 2.11/0.98  --res_lit_sel_side                      none
% 2.11/0.98  --res_ordering                          kbo
% 2.11/0.98  --res_to_prop_solver                    active
% 2.11/0.98  --res_prop_simpl_new                    false
% 2.11/0.98  --res_prop_simpl_given                  true
% 2.11/0.98  --res_passive_queue_type                priority_queues
% 2.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.98  --res_passive_queues_freq               [15;5]
% 2.11/0.98  --res_forward_subs                      full
% 2.11/0.98  --res_backward_subs                     full
% 2.11/0.98  --res_forward_subs_resolution           true
% 2.11/0.98  --res_backward_subs_resolution          true
% 2.11/0.98  --res_orphan_elimination                true
% 2.11/0.98  --res_time_limit                        2.
% 2.11/0.98  --res_out_proof                         true
% 2.11/0.98  
% 2.11/0.98  ------ Superposition Options
% 2.11/0.98  
% 2.11/0.98  --superposition_flag                    true
% 2.11/0.98  --sup_passive_queue_type                priority_queues
% 2.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.98  --demod_completeness_check              fast
% 2.11/0.98  --demod_use_ground                      true
% 2.11/0.98  --sup_to_prop_solver                    passive
% 2.11/0.98  --sup_prop_simpl_new                    true
% 2.11/0.98  --sup_prop_simpl_given                  true
% 2.11/0.98  --sup_fun_splitting                     false
% 2.11/0.98  --sup_smt_interval                      50000
% 2.11/0.98  
% 2.11/0.98  ------ Superposition Simplification Setup
% 2.11/0.98  
% 2.11/0.98  --sup_indices_passive                   []
% 2.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_full_bw                           [BwDemod]
% 2.11/0.98  --sup_immed_triv                        [TrivRules]
% 2.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_immed_bw_main                     []
% 2.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.98  
% 2.11/0.98  ------ Combination Options
% 2.11/0.98  
% 2.11/0.98  --comb_res_mult                         3
% 2.11/0.98  --comb_sup_mult                         2
% 2.11/0.98  --comb_inst_mult                        10
% 2.11/0.98  
% 2.11/0.98  ------ Debug Options
% 2.11/0.98  
% 2.11/0.98  --dbg_backtrace                         false
% 2.11/0.98  --dbg_dump_prop_clauses                 false
% 2.11/0.98  --dbg_dump_prop_clauses_file            -
% 2.11/0.98  --dbg_out_stat                          false
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  ------ Proving...
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  % SZS status Theorem for theBenchmark.p
% 2.11/0.98  
% 2.11/0.98   Resolution empty clause
% 2.11/0.98  
% 2.11/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/0.98  
% 2.11/0.98  fof(f23,conjecture,(
% 2.11/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f24,negated_conjecture,(
% 2.11/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.11/0.98    inference(negated_conjecture,[],[f23])).
% 2.11/0.98  
% 2.11/0.98  fof(f40,plain,(
% 2.11/0.98    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.11/0.98    inference(ennf_transformation,[],[f24])).
% 2.11/0.98  
% 2.11/0.98  fof(f41,plain,(
% 2.11/0.98    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.11/0.98    inference(flattening,[],[f40])).
% 2.11/0.98  
% 2.11/0.98  fof(f45,plain,(
% 2.11/0.98    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & k1_relset_1(sK0,sK1,sK2) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 2.11/0.98    introduced(choice_axiom,[])).
% 2.11/0.98  
% 2.11/0.98  fof(f46,plain,(
% 2.11/0.98    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & k1_relset_1(sK0,sK1,sK2) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 2.11/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45])).
% 2.11/0.98  
% 2.11/0.98  fof(f82,plain,(
% 2.11/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.11/0.98    inference(cnf_transformation,[],[f46])).
% 2.11/0.98  
% 2.11/0.98  fof(f21,axiom,(
% 2.11/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f36,plain,(
% 2.11/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.98    inference(ennf_transformation,[],[f21])).
% 2.11/0.98  
% 2.11/0.98  fof(f37,plain,(
% 2.11/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.98    inference(flattening,[],[f36])).
% 2.11/0.98  
% 2.11/0.98  fof(f44,plain,(
% 2.11/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.98    inference(nnf_transformation,[],[f37])).
% 2.11/0.98  
% 2.11/0.98  fof(f74,plain,(
% 2.11/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.98    inference(cnf_transformation,[],[f44])).
% 2.11/0.98  
% 2.11/0.98  fof(f84,plain,(
% 2.11/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.11/0.98    inference(cnf_transformation,[],[f46])).
% 2.11/0.98  
% 2.11/0.98  fof(f81,plain,(
% 2.11/0.98    v1_funct_1(sK2)),
% 2.11/0.98    inference(cnf_transformation,[],[f46])).
% 2.11/0.98  
% 2.11/0.98  fof(f83,plain,(
% 2.11/0.98    k1_relset_1(sK0,sK1,sK2) = sK0),
% 2.11/0.98    inference(cnf_transformation,[],[f46])).
% 2.11/0.98  
% 2.11/0.98  fof(f5,axiom,(
% 2.11/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f42,plain,(
% 2.11/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.11/0.98    inference(nnf_transformation,[],[f5])).
% 2.11/0.98  
% 2.11/0.98  fof(f43,plain,(
% 2.11/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.11/0.98    inference(flattening,[],[f42])).
% 2.11/0.98  
% 2.11/0.98  fof(f53,plain,(
% 2.11/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.11/0.98    inference(cnf_transformation,[],[f43])).
% 2.11/0.98  
% 2.11/0.98  fof(f85,plain,(
% 2.11/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.11/0.98    inference(equality_resolution,[],[f53])).
% 2.11/0.98  
% 2.11/0.98  fof(f19,axiom,(
% 2.11/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f34,plain,(
% 2.11/0.98    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.98    inference(ennf_transformation,[],[f19])).
% 2.11/0.98  
% 2.11/0.98  fof(f70,plain,(
% 2.11/0.98    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.98    inference(cnf_transformation,[],[f34])).
% 2.11/0.98  
% 2.11/0.98  fof(f16,axiom,(
% 2.11/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f67,plain,(
% 2.11/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.11/0.98    inference(cnf_transformation,[],[f16])).
% 2.11/0.98  
% 2.11/0.98  fof(f11,axiom,(
% 2.11/0.98    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f59,plain,(
% 2.11/0.98    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.11/0.98    inference(cnf_transformation,[],[f11])).
% 2.11/0.98  
% 2.11/0.98  fof(f75,plain,(
% 2.11/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.98    inference(cnf_transformation,[],[f44])).
% 2.11/0.98  
% 2.11/0.98  fof(f90,plain,(
% 2.11/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.11/0.98    inference(equality_resolution,[],[f75])).
% 2.11/0.98  
% 2.11/0.98  fof(f52,plain,(
% 2.11/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.11/0.98    inference(cnf_transformation,[],[f43])).
% 2.11/0.98  
% 2.11/0.98  fof(f86,plain,(
% 2.11/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.11/0.98    inference(equality_resolution,[],[f52])).
% 2.11/0.98  
% 2.11/0.98  fof(f77,plain,(
% 2.11/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.98    inference(cnf_transformation,[],[f44])).
% 2.11/0.98  
% 2.11/0.98  fof(f87,plain,(
% 2.11/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.98    inference(equality_resolution,[],[f77])).
% 2.11/0.98  
% 2.11/0.98  fof(f88,plain,(
% 2.11/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.11/0.98    inference(equality_resolution,[],[f87])).
% 2.11/0.98  
% 2.11/0.98  fof(f6,axiom,(
% 2.11/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.98  
% 2.11/0.98  fof(f54,plain,(
% 2.11/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.11/0.98    inference(cnf_transformation,[],[f6])).
% 2.11/0.98  
% 2.11/0.98  cnf(c_36,negated_conjecture,
% 2.11/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.11/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1759,plain,
% 2.11/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.11/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_28,plain,
% 2.11/0.98      ( v1_funct_2(X0,X1,X2)
% 2.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.11/0.98      | k1_xboole_0 = X2 ),
% 2.11/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_34,negated_conjecture,
% 2.11/0.98      ( ~ v1_funct_2(sK2,sK0,sK1)
% 2.11/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.11/0.98      | ~ v1_funct_1(sK2) ),
% 2.11/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_37,negated_conjecture,
% 2.11/0.98      ( v1_funct_1(sK2) ),
% 2.11/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_162,negated_conjecture,
% 2.11/0.98      ( ~ v1_funct_2(sK2,sK0,sK1) ),
% 2.11/0.98      inference(global_propositional_subsumption,
% 2.11/0.98                [status(thm)],
% 2.11/0.98                [c_34,c_37,c_36]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_437,plain,
% 2.11/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.11/0.98      | sK1 != X2
% 2.11/0.98      | sK0 != X1
% 2.11/0.98      | sK2 != X0
% 2.11/0.98      | k1_xboole_0 = X2 ),
% 2.11/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_162]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_438,plain,
% 2.11/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.11/0.98      | k1_relset_1(sK0,sK1,sK2) != sK0
% 2.11/0.98      | k1_xboole_0 = sK1 ),
% 2.11/0.98      inference(unflattening,[status(thm)],[c_437]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_35,negated_conjecture,
% 2.11/0.98      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_440,plain,
% 2.11/0.98      ( k1_xboole_0 = sK1 ),
% 2.11/0.98      inference(global_propositional_subsumption,
% 2.11/0.98                [status(thm)],
% 2.11/0.98                [c_438,c_36,c_35]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1808,plain,
% 2.11/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_1759,c_440]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_4,plain,
% 2.11/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1809,plain,
% 2.11/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_1808,c_4]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_23,plain,
% 2.11/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.11/0.98      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1761,plain,
% 2.11/0.98      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 2.11/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.11/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3239,plain,
% 2.11/0.98      ( k9_relat_1(k6_relat_1(k1_xboole_0),sK2) = sK2 ),
% 2.11/0.98      inference(superposition,[status(thm)],[c_1809,c_1761]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_20,plain,
% 2.11/0.98      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3241,plain,
% 2.11/0.98      ( k9_relat_1(k1_xboole_0,sK2) = sK2 ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_3239,c_20]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_12,plain,
% 2.11/0.98      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3242,plain,
% 2.11/0.98      ( sK2 = k1_xboole_0 ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_3241,c_12]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_27,plain,
% 2.11/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.11/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_403,plain,
% 2.11/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.11/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.11/0.98      | sK1 != X1
% 2.11/0.98      | sK0 != k1_xboole_0
% 2.11/0.98      | sK2 != X0 ),
% 2.11/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_162]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_404,plain,
% 2.11/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.11/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0 ),
% 2.11/0.98      inference(unflattening,[status(thm)],[c_403]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1755,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0
% 2.11/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.11/0.98      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1869,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0
% 2.11/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_1755,c_440]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_5,plain,
% 2.11/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1870,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0
% 2.11/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_1869,c_5]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1874,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0 ),
% 2.11/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1870,c_1809]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3260,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.11/0.98      | sK0 != k1_xboole_0 ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_3242,c_1874]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_25,plain,
% 2.11/0.98      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.11/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.11/0.98      | k1_xboole_0 = X0 ),
% 2.11/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_356,plain,
% 2.11/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.11/0.98      | sK1 != k1_xboole_0
% 2.11/0.98      | sK0 != X0
% 2.11/0.98      | sK2 != k1_xboole_0
% 2.11/0.98      | k1_xboole_0 = X0 ),
% 2.11/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_162]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_357,plain,
% 2.11/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.11/0.98      | sK1 != k1_xboole_0
% 2.11/0.98      | sK2 != k1_xboole_0
% 2.11/0.98      | k1_xboole_0 = sK0 ),
% 2.11/0.98      inference(unflattening,[status(thm)],[c_356]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_7,plain,
% 2.11/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.11/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_367,plain,
% 2.11/0.98      ( sK1 != k1_xboole_0 | sK2 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.11/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_357,c_7]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1825,plain,
% 2.11/0.98      ( sK0 = k1_xboole_0 | sK2 != k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_367,c_440]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1826,plain,
% 2.11/0.98      ( sK0 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.11/0.98      inference(equality_resolution_simp,[status(thm)],[c_1825]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3261,plain,
% 2.11/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_3242,c_1826]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3284,plain,
% 2.11/0.98      ( sK0 = k1_xboole_0 ),
% 2.11/0.98      inference(equality_resolution_simp,[status(thm)],[c_3261]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_1799,plain,
% 2.11/0.98      ( k1_relset_1(sK0,k1_xboole_0,sK2) = sK0 ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_35,c_440]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3265,plain,
% 2.11/0.98      ( k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) = sK0 ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_3242,c_1799]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3287,plain,
% 2.11/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.11/0.98      inference(demodulation,[status(thm)],[c_3284,c_3265]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3296,plain,
% 2.11/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.11/0.98      inference(light_normalisation,[status(thm)],[c_3260,c_3284,c_3287]) ).
% 2.11/0.98  
% 2.11/0.98  cnf(c_3297,plain,
% 2.11/0.98      ( $false ),
% 2.11/0.98      inference(equality_resolution_simp,[status(thm)],[c_3296]) ).
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/0.98  
% 2.11/0.98  ------                               Statistics
% 2.11/0.98  
% 2.11/0.98  ------ General
% 2.11/0.98  
% 2.11/0.98  abstr_ref_over_cycles:                  0
% 2.11/0.98  abstr_ref_under_cycles:                 0
% 2.11/0.98  gc_basic_clause_elim:                   0
% 2.11/0.98  forced_gc_time:                         0
% 2.11/0.98  parsing_time:                           0.009
% 2.11/0.98  unif_index_cands_time:                  0.
% 2.11/0.98  unif_index_add_time:                    0.
% 2.11/0.98  orderings_time:                         0.
% 2.11/0.98  out_proof_time:                         0.01
% 2.11/0.98  total_time:                             0.127
% 2.11/0.98  num_of_symbols:                         51
% 2.11/0.98  num_of_terms:                           2681
% 2.11/0.98  
% 2.11/0.98  ------ Preprocessing
% 2.11/0.98  
% 2.11/0.98  num_of_splits:                          1
% 2.11/0.98  num_of_split_atoms:                     1
% 2.11/0.98  num_of_reused_defs:                     0
% 2.11/0.98  num_eq_ax_congr_red:                    3
% 2.11/0.98  num_of_sem_filtered_clauses:            1
% 2.11/0.98  num_of_subtypes:                        0
% 2.11/0.98  monotx_restored_types:                  0
% 2.11/0.98  sat_num_of_epr_types:                   0
% 2.11/0.98  sat_num_of_non_cyclic_types:            0
% 2.11/0.98  sat_guarded_non_collapsed_types:        0
% 2.11/0.98  num_pure_diseq_elim:                    0
% 2.11/0.98  simp_replaced_by:                       0
% 2.11/0.98  res_preprocessed:                       175
% 2.11/0.98  prep_upred:                             0
% 2.11/0.98  prep_unflattend:                        76
% 2.11/0.98  smt_new_axioms:                         0
% 2.11/0.98  pred_elim_cands:                        4
% 2.11/0.98  pred_elim:                              2
% 2.11/0.98  pred_elim_cl:                           2
% 2.11/0.98  pred_elim_cycles:                       4
% 2.11/0.98  merged_defs:                            0
% 2.11/0.98  merged_defs_ncl:                        0
% 2.11/0.98  bin_hyper_res:                          0
% 2.11/0.98  prep_cycles:                            4
% 2.11/0.98  pred_elim_time:                         0.021
% 2.11/0.98  splitting_time:                         0.
% 2.11/0.98  sem_filter_time:                        0.
% 2.11/0.98  monotx_time:                            0.
% 2.11/0.98  subtype_inf_time:                       0.
% 2.11/0.98  
% 2.11/0.98  ------ Problem properties
% 2.11/0.98  
% 2.11/0.98  clauses:                                36
% 2.11/0.98  conjectures:                            3
% 2.11/0.98  epr:                                    4
% 2.11/0.98  horn:                                   33
% 2.11/0.98  ground:                                 11
% 2.11/0.98  unary:                                  18
% 2.11/0.98  binary:                                 5
% 2.11/0.98  lits:                                   74
% 2.11/0.98  lits_eq:                                34
% 2.11/0.98  fd_pure:                                0
% 2.11/0.98  fd_pseudo:                              0
% 2.11/0.98  fd_cond:                                2
% 2.11/0.98  fd_pseudo_cond:                         0
% 2.11/0.98  ac_symbols:                             0
% 2.11/0.98  
% 2.11/0.98  ------ Propositional Solver
% 2.11/0.98  
% 2.11/0.98  prop_solver_calls:                      26
% 2.11/0.98  prop_fast_solver_calls:                 1025
% 2.11/0.98  smt_solver_calls:                       0
% 2.11/0.98  smt_fast_solver_calls:                  0
% 2.11/0.98  prop_num_of_clauses:                    938
% 2.11/0.98  prop_preprocess_simplified:             4885
% 2.11/0.98  prop_fo_subsumed:                       14
% 2.11/0.98  prop_solver_time:                       0.
% 2.11/0.98  smt_solver_time:                        0.
% 2.11/0.98  smt_fast_solver_time:                   0.
% 2.11/0.98  prop_fast_solver_time:                  0.
% 2.11/0.98  prop_unsat_core_time:                   0.
% 2.11/0.98  
% 2.11/0.98  ------ QBF
% 2.11/0.98  
% 2.11/0.98  qbf_q_res:                              0
% 2.11/0.98  qbf_num_tautologies:                    0
% 2.11/0.98  qbf_prep_cycles:                        0
% 2.11/0.98  
% 2.11/0.98  ------ BMC1
% 2.11/0.98  
% 2.11/0.98  bmc1_current_bound:                     -1
% 2.11/0.98  bmc1_last_solved_bound:                 -1
% 2.11/0.98  bmc1_unsat_core_size:                   -1
% 2.11/0.98  bmc1_unsat_core_parents_size:           -1
% 2.11/0.98  bmc1_merge_next_fun:                    0
% 2.11/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.11/0.98  
% 2.11/0.98  ------ Instantiation
% 2.11/0.98  
% 2.11/0.98  inst_num_of_clauses:                    280
% 2.11/0.98  inst_num_in_passive:                    44
% 2.11/0.98  inst_num_in_active:                     166
% 2.11/0.98  inst_num_in_unprocessed:                70
% 2.11/0.98  inst_num_of_loops:                      190
% 2.11/0.98  inst_num_of_learning_restarts:          0
% 2.11/0.98  inst_num_moves_active_passive:          22
% 2.11/0.98  inst_lit_activity:                      0
% 2.11/0.98  inst_lit_activity_moves:                0
% 2.11/0.98  inst_num_tautologies:                   0
% 2.11/0.98  inst_num_prop_implied:                  0
% 2.11/0.98  inst_num_existing_simplified:           0
% 2.11/0.98  inst_num_eq_res_simplified:             0
% 2.11/0.98  inst_num_child_elim:                    0
% 2.11/0.98  inst_num_of_dismatching_blockings:      15
% 2.11/0.98  inst_num_of_non_proper_insts:           168
% 2.11/0.98  inst_num_of_duplicates:                 0
% 2.11/0.98  inst_inst_num_from_inst_to_res:         0
% 2.11/0.98  inst_dismatching_checking_time:         0.
% 2.11/0.98  
% 2.11/0.98  ------ Resolution
% 2.11/0.98  
% 2.11/0.98  res_num_of_clauses:                     0
% 2.11/0.98  res_num_in_passive:                     0
% 2.11/0.98  res_num_in_active:                      0
% 2.11/0.98  res_num_of_loops:                       179
% 2.11/0.98  res_forward_subset_subsumed:            8
% 2.11/0.98  res_backward_subset_subsumed:           0
% 2.11/0.98  res_forward_subsumed:                   0
% 2.11/0.98  res_backward_subsumed:                  0
% 2.11/0.98  res_forward_subsumption_resolution:     1
% 2.11/0.98  res_backward_subsumption_resolution:    0
% 2.11/0.98  res_clause_to_clause_subsumption:       98
% 2.11/0.98  res_orphan_elimination:                 0
% 2.11/0.98  res_tautology_del:                      24
% 2.11/0.98  res_num_eq_res_simplified:              0
% 2.11/0.98  res_num_sel_changes:                    0
% 2.11/0.98  res_moves_from_active_to_pass:          0
% 2.11/0.98  
% 2.11/0.98  ------ Superposition
% 2.11/0.98  
% 2.11/0.98  sup_time_total:                         0.
% 2.11/0.98  sup_time_generating:                    0.
% 2.11/0.98  sup_time_sim_full:                      0.
% 2.11/0.98  sup_time_sim_immed:                     0.
% 2.11/0.98  
% 2.11/0.98  sup_num_of_clauses:                     45
% 2.11/0.98  sup_num_in_active:                      27
% 2.11/0.98  sup_num_in_passive:                     18
% 2.11/0.98  sup_num_of_loops:                       37
% 2.11/0.98  sup_fw_superposition:                   34
% 2.11/0.98  sup_bw_superposition:                   10
% 2.11/0.98  sup_immediate_simplified:               6
% 2.11/0.98  sup_given_eliminated:                   0
% 2.11/0.98  comparisons_done:                       0
% 2.11/0.98  comparisons_avoided:                    3
% 2.11/0.98  
% 2.11/0.98  ------ Simplifications
% 2.11/0.98  
% 2.11/0.98  
% 2.11/0.98  sim_fw_subset_subsumed:                 1
% 2.11/0.98  sim_bw_subset_subsumed:                 0
% 2.11/0.98  sim_fw_subsumed:                        1
% 2.11/0.98  sim_bw_subsumed:                        0
% 2.11/0.98  sim_fw_subsumption_res:                 1
% 2.11/0.98  sim_bw_subsumption_res:                 0
% 2.11/0.98  sim_tautology_del:                      1
% 2.11/0.98  sim_eq_tautology_del:                   1
% 2.11/0.98  sim_eq_res_simp:                        3
% 2.11/0.98  sim_fw_demodulated:                     7
% 2.11/0.98  sim_bw_demodulated:                     12
% 2.11/0.98  sim_light_normalised:                   13
% 2.11/0.98  sim_joinable_taut:                      0
% 2.11/0.98  sim_joinable_simp:                      0
% 2.11/0.98  sim_ac_normalised:                      0
% 2.11/0.98  sim_smt_subsumption:                    0
% 2.11/0.98  
%------------------------------------------------------------------------------
