%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:27 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 110 expanded)
%              Number of clauses        :   39 (  45 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 231 expanded)
%              Number of equality atoms :   86 ( 131 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_498,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_493,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_1390,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_493])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_497,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_699,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_497])).

cnf(c_1441,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_699])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_496,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_830,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_699,c_496])).

cnf(c_1445,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1441,c_830])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1446,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1445,c_11])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_495,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1078,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_498,c_495])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_494,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_511,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_494,c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_142])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_491,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_796,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_511,c_491])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_942,plain,
    ( k7_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_796,c_15])).

cnf(c_1095,plain,
    ( k9_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1078,c_942])).

cnf(c_1450,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1446,c_1095])).

cnf(c_1451,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1450])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.40/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/0.95  
% 1.40/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.40/0.95  
% 1.40/0.95  ------  iProver source info
% 1.40/0.95  
% 1.40/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.40/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.40/0.95  git: non_committed_changes: false
% 1.40/0.95  git: last_make_outside_of_git: false
% 1.40/0.95  
% 1.40/0.95  ------ 
% 1.40/0.95  
% 1.40/0.95  ------ Input Options
% 1.40/0.95  
% 1.40/0.95  --out_options                           all
% 1.40/0.95  --tptp_safe_out                         true
% 1.40/0.95  --problem_path                          ""
% 1.40/0.95  --include_path                          ""
% 1.40/0.95  --clausifier                            res/vclausify_rel
% 1.40/0.95  --clausifier_options                    --mode clausify
% 1.40/0.95  --stdin                                 false
% 1.40/0.95  --stats_out                             all
% 1.40/0.95  
% 1.40/0.95  ------ General Options
% 1.40/0.95  
% 1.40/0.95  --fof                                   false
% 1.40/0.95  --time_out_real                         305.
% 1.40/0.95  --time_out_virtual                      -1.
% 1.40/0.95  --symbol_type_check                     false
% 1.40/0.95  --clausify_out                          false
% 1.40/0.95  --sig_cnt_out                           false
% 1.40/0.95  --trig_cnt_out                          false
% 1.40/0.95  --trig_cnt_out_tolerance                1.
% 1.40/0.95  --trig_cnt_out_sk_spl                   false
% 1.40/0.95  --abstr_cl_out                          false
% 1.40/0.95  
% 1.40/0.95  ------ Global Options
% 1.40/0.95  
% 1.40/0.95  --schedule                              default
% 1.40/0.95  --add_important_lit                     false
% 1.40/0.95  --prop_solver_per_cl                    1000
% 1.40/0.95  --min_unsat_core                        false
% 1.40/0.95  --soft_assumptions                      false
% 1.40/0.95  --soft_lemma_size                       3
% 1.40/0.95  --prop_impl_unit_size                   0
% 1.40/0.95  --prop_impl_unit                        []
% 1.40/0.95  --share_sel_clauses                     true
% 1.40/0.95  --reset_solvers                         false
% 1.40/0.95  --bc_imp_inh                            [conj_cone]
% 1.40/0.95  --conj_cone_tolerance                   3.
% 1.40/0.95  --extra_neg_conj                        none
% 1.40/0.95  --large_theory_mode                     true
% 1.40/0.95  --prolific_symb_bound                   200
% 1.40/0.95  --lt_threshold                          2000
% 1.40/0.95  --clause_weak_htbl                      true
% 1.40/0.95  --gc_record_bc_elim                     false
% 1.40/0.95  
% 1.40/0.95  ------ Preprocessing Options
% 1.40/0.95  
% 1.40/0.95  --preprocessing_flag                    true
% 1.40/0.95  --time_out_prep_mult                    0.1
% 1.40/0.95  --splitting_mode                        input
% 1.40/0.95  --splitting_grd                         true
% 1.40/0.95  --splitting_cvd                         false
% 1.40/0.95  --splitting_cvd_svl                     false
% 1.40/0.95  --splitting_nvd                         32
% 1.40/0.95  --sub_typing                            true
% 1.40/0.95  --prep_gs_sim                           true
% 1.40/0.95  --prep_unflatten                        true
% 1.40/0.95  --prep_res_sim                          true
% 1.40/0.95  --prep_upred                            true
% 1.40/0.95  --prep_sem_filter                       exhaustive
% 1.40/0.95  --prep_sem_filter_out                   false
% 1.40/0.95  --pred_elim                             true
% 1.40/0.95  --res_sim_input                         true
% 1.40/0.95  --eq_ax_congr_red                       true
% 1.40/0.95  --pure_diseq_elim                       true
% 1.40/0.95  --brand_transform                       false
% 1.40/0.95  --non_eq_to_eq                          false
% 1.40/0.95  --prep_def_merge                        true
% 1.40/0.95  --prep_def_merge_prop_impl              false
% 1.40/0.95  --prep_def_merge_mbd                    true
% 1.40/0.95  --prep_def_merge_tr_red                 false
% 1.40/0.95  --prep_def_merge_tr_cl                  false
% 1.40/0.95  --smt_preprocessing                     true
% 1.40/0.95  --smt_ac_axioms                         fast
% 1.40/0.95  --preprocessed_out                      false
% 1.40/0.95  --preprocessed_stats                    false
% 1.40/0.95  
% 1.40/0.95  ------ Abstraction refinement Options
% 1.40/0.95  
% 1.40/0.95  --abstr_ref                             []
% 1.40/0.95  --abstr_ref_prep                        false
% 1.40/0.95  --abstr_ref_until_sat                   false
% 1.40/0.95  --abstr_ref_sig_restrict                funpre
% 1.40/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.95  --abstr_ref_under                       []
% 1.40/0.95  
% 1.40/0.95  ------ SAT Options
% 1.40/0.95  
% 1.40/0.95  --sat_mode                              false
% 1.40/0.95  --sat_fm_restart_options                ""
% 1.40/0.95  --sat_gr_def                            false
% 1.40/0.95  --sat_epr_types                         true
% 1.40/0.95  --sat_non_cyclic_types                  false
% 1.40/0.95  --sat_finite_models                     false
% 1.40/0.95  --sat_fm_lemmas                         false
% 1.40/0.95  --sat_fm_prep                           false
% 1.40/0.95  --sat_fm_uc_incr                        true
% 1.40/0.95  --sat_out_model                         small
% 1.40/0.95  --sat_out_clauses                       false
% 1.40/0.95  
% 1.40/0.95  ------ QBF Options
% 1.40/0.95  
% 1.40/0.95  --qbf_mode                              false
% 1.40/0.95  --qbf_elim_univ                         false
% 1.40/0.95  --qbf_dom_inst                          none
% 1.40/0.95  --qbf_dom_pre_inst                      false
% 1.40/0.95  --qbf_sk_in                             false
% 1.40/0.95  --qbf_pred_elim                         true
% 1.40/0.95  --qbf_split                             512
% 1.40/0.95  
% 1.40/0.95  ------ BMC1 Options
% 1.40/0.95  
% 1.40/0.95  --bmc1_incremental                      false
% 1.40/0.95  --bmc1_axioms                           reachable_all
% 1.40/0.95  --bmc1_min_bound                        0
% 1.40/0.95  --bmc1_max_bound                        -1
% 1.40/0.95  --bmc1_max_bound_default                -1
% 1.40/0.95  --bmc1_symbol_reachability              true
% 1.40/0.95  --bmc1_property_lemmas                  false
% 1.40/0.95  --bmc1_k_induction                      false
% 1.40/0.95  --bmc1_non_equiv_states                 false
% 1.40/0.95  --bmc1_deadlock                         false
% 1.40/0.95  --bmc1_ucm                              false
% 1.40/0.95  --bmc1_add_unsat_core                   none
% 1.40/0.95  --bmc1_unsat_core_children              false
% 1.40/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.95  --bmc1_out_stat                         full
% 1.40/0.95  --bmc1_ground_init                      false
% 1.40/0.95  --bmc1_pre_inst_next_state              false
% 1.40/0.95  --bmc1_pre_inst_state                   false
% 1.40/0.95  --bmc1_pre_inst_reach_state             false
% 1.40/0.95  --bmc1_out_unsat_core                   false
% 1.40/0.95  --bmc1_aig_witness_out                  false
% 1.40/0.95  --bmc1_verbose                          false
% 1.40/0.95  --bmc1_dump_clauses_tptp                false
% 1.40/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.95  --bmc1_dump_file                        -
% 1.40/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.95  --bmc1_ucm_extend_mode                  1
% 1.40/0.95  --bmc1_ucm_init_mode                    2
% 1.40/0.95  --bmc1_ucm_cone_mode                    none
% 1.40/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.95  --bmc1_ucm_relax_model                  4
% 1.40/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.95  --bmc1_ucm_layered_model                none
% 1.40/0.95  --bmc1_ucm_max_lemma_size               10
% 1.40/0.95  
% 1.40/0.95  ------ AIG Options
% 1.40/0.95  
% 1.40/0.95  --aig_mode                              false
% 1.40/0.95  
% 1.40/0.95  ------ Instantiation Options
% 1.40/0.95  
% 1.40/0.95  --instantiation_flag                    true
% 1.40/0.95  --inst_sos_flag                         false
% 1.40/0.95  --inst_sos_phase                        true
% 1.40/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.95  --inst_lit_sel_side                     num_symb
% 1.40/0.95  --inst_solver_per_active                1400
% 1.40/0.95  --inst_solver_calls_frac                1.
% 1.40/0.95  --inst_passive_queue_type               priority_queues
% 1.40/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.95  --inst_passive_queues_freq              [25;2]
% 1.40/0.95  --inst_dismatching                      true
% 1.40/0.95  --inst_eager_unprocessed_to_passive     true
% 1.40/0.95  --inst_prop_sim_given                   true
% 1.40/0.95  --inst_prop_sim_new                     false
% 1.40/0.95  --inst_subs_new                         false
% 1.40/0.95  --inst_eq_res_simp                      false
% 1.40/0.95  --inst_subs_given                       false
% 1.40/0.95  --inst_orphan_elimination               true
% 1.40/0.95  --inst_learning_loop_flag               true
% 1.40/0.95  --inst_learning_start                   3000
% 1.40/0.95  --inst_learning_factor                  2
% 1.40/0.95  --inst_start_prop_sim_after_learn       3
% 1.40/0.95  --inst_sel_renew                        solver
% 1.40/0.95  --inst_lit_activity_flag                true
% 1.40/0.95  --inst_restr_to_given                   false
% 1.40/0.95  --inst_activity_threshold               500
% 1.40/0.95  --inst_out_proof                        true
% 1.40/0.95  
% 1.40/0.95  ------ Resolution Options
% 1.40/0.95  
% 1.40/0.95  --resolution_flag                       true
% 1.40/0.95  --res_lit_sel                           adaptive
% 1.40/0.95  --res_lit_sel_side                      none
% 1.40/0.95  --res_ordering                          kbo
% 1.40/0.95  --res_to_prop_solver                    active
% 1.40/0.95  --res_prop_simpl_new                    false
% 1.40/0.95  --res_prop_simpl_given                  true
% 1.40/0.95  --res_passive_queue_type                priority_queues
% 1.40/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.95  --res_passive_queues_freq               [15;5]
% 1.40/0.95  --res_forward_subs                      full
% 1.40/0.95  --res_backward_subs                     full
% 1.40/0.95  --res_forward_subs_resolution           true
% 1.40/0.95  --res_backward_subs_resolution          true
% 1.40/0.95  --res_orphan_elimination                true
% 1.40/0.95  --res_time_limit                        2.
% 1.40/0.95  --res_out_proof                         true
% 1.40/0.95  
% 1.40/0.95  ------ Superposition Options
% 1.40/0.95  
% 1.40/0.95  --superposition_flag                    true
% 1.40/0.95  --sup_passive_queue_type                priority_queues
% 1.40/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.95  --demod_completeness_check              fast
% 1.40/0.95  --demod_use_ground                      true
% 1.40/0.95  --sup_to_prop_solver                    passive
% 1.40/0.95  --sup_prop_simpl_new                    true
% 1.40/0.95  --sup_prop_simpl_given                  true
% 1.40/0.95  --sup_fun_splitting                     false
% 1.40/0.95  --sup_smt_interval                      50000
% 1.40/0.95  
% 1.40/0.95  ------ Superposition Simplification Setup
% 1.40/0.95  
% 1.40/0.95  --sup_indices_passive                   []
% 1.40/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_full_bw                           [BwDemod]
% 1.40/0.95  --sup_immed_triv                        [TrivRules]
% 1.40/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_immed_bw_main                     []
% 1.40/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.95  
% 1.40/0.95  ------ Combination Options
% 1.40/0.95  
% 1.40/0.95  --comb_res_mult                         3
% 1.40/0.95  --comb_sup_mult                         2
% 1.40/0.95  --comb_inst_mult                        10
% 1.40/0.95  
% 1.40/0.95  ------ Debug Options
% 1.40/0.95  
% 1.40/0.95  --dbg_backtrace                         false
% 1.40/0.95  --dbg_dump_prop_clauses                 false
% 1.40/0.95  --dbg_dump_prop_clauses_file            -
% 1.40/0.95  --dbg_out_stat                          false
% 1.40/0.95  ------ Parsing...
% 1.40/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.40/0.95  
% 1.40/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.40/0.95  
% 1.40/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.40/0.95  
% 1.40/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.40/0.95  ------ Proving...
% 1.40/0.95  ------ Problem Properties 
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  clauses                                 14
% 1.40/0.95  conjectures                             2
% 1.40/0.95  EPR                                     0
% 1.40/0.95  Horn                                    12
% 1.40/0.95  unary                                   8
% 1.40/0.95  binary                                  3
% 1.40/0.95  lits                                    23
% 1.40/0.95  lits eq                                 13
% 1.40/0.95  fd_pure                                 0
% 1.40/0.95  fd_pseudo                               0
% 1.40/0.95  fd_cond                                 3
% 1.40/0.95  fd_pseudo_cond                          0
% 1.40/0.95  AC symbols                              0
% 1.40/0.95  
% 1.40/0.95  ------ Schedule dynamic 5 is on 
% 1.40/0.95  
% 1.40/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  ------ 
% 1.40/0.95  Current options:
% 1.40/0.95  ------ 
% 1.40/0.95  
% 1.40/0.95  ------ Input Options
% 1.40/0.95  
% 1.40/0.95  --out_options                           all
% 1.40/0.95  --tptp_safe_out                         true
% 1.40/0.95  --problem_path                          ""
% 1.40/0.95  --include_path                          ""
% 1.40/0.95  --clausifier                            res/vclausify_rel
% 1.40/0.95  --clausifier_options                    --mode clausify
% 1.40/0.95  --stdin                                 false
% 1.40/0.95  --stats_out                             all
% 1.40/0.95  
% 1.40/0.95  ------ General Options
% 1.40/0.95  
% 1.40/0.95  --fof                                   false
% 1.40/0.95  --time_out_real                         305.
% 1.40/0.95  --time_out_virtual                      -1.
% 1.40/0.95  --symbol_type_check                     false
% 1.40/0.95  --clausify_out                          false
% 1.40/0.95  --sig_cnt_out                           false
% 1.40/0.95  --trig_cnt_out                          false
% 1.40/0.95  --trig_cnt_out_tolerance                1.
% 1.40/0.95  --trig_cnt_out_sk_spl                   false
% 1.40/0.95  --abstr_cl_out                          false
% 1.40/0.95  
% 1.40/0.95  ------ Global Options
% 1.40/0.95  
% 1.40/0.95  --schedule                              default
% 1.40/0.95  --add_important_lit                     false
% 1.40/0.95  --prop_solver_per_cl                    1000
% 1.40/0.95  --min_unsat_core                        false
% 1.40/0.95  --soft_assumptions                      false
% 1.40/0.95  --soft_lemma_size                       3
% 1.40/0.95  --prop_impl_unit_size                   0
% 1.40/0.95  --prop_impl_unit                        []
% 1.40/0.95  --share_sel_clauses                     true
% 1.40/0.95  --reset_solvers                         false
% 1.40/0.95  --bc_imp_inh                            [conj_cone]
% 1.40/0.95  --conj_cone_tolerance                   3.
% 1.40/0.95  --extra_neg_conj                        none
% 1.40/0.95  --large_theory_mode                     true
% 1.40/0.95  --prolific_symb_bound                   200
% 1.40/0.95  --lt_threshold                          2000
% 1.40/0.95  --clause_weak_htbl                      true
% 1.40/0.95  --gc_record_bc_elim                     false
% 1.40/0.95  
% 1.40/0.95  ------ Preprocessing Options
% 1.40/0.95  
% 1.40/0.95  --preprocessing_flag                    true
% 1.40/0.95  --time_out_prep_mult                    0.1
% 1.40/0.95  --splitting_mode                        input
% 1.40/0.95  --splitting_grd                         true
% 1.40/0.95  --splitting_cvd                         false
% 1.40/0.95  --splitting_cvd_svl                     false
% 1.40/0.95  --splitting_nvd                         32
% 1.40/0.95  --sub_typing                            true
% 1.40/0.95  --prep_gs_sim                           true
% 1.40/0.95  --prep_unflatten                        true
% 1.40/0.95  --prep_res_sim                          true
% 1.40/0.95  --prep_upred                            true
% 1.40/0.95  --prep_sem_filter                       exhaustive
% 1.40/0.95  --prep_sem_filter_out                   false
% 1.40/0.95  --pred_elim                             true
% 1.40/0.95  --res_sim_input                         true
% 1.40/0.95  --eq_ax_congr_red                       true
% 1.40/0.95  --pure_diseq_elim                       true
% 1.40/0.95  --brand_transform                       false
% 1.40/0.95  --non_eq_to_eq                          false
% 1.40/0.95  --prep_def_merge                        true
% 1.40/0.95  --prep_def_merge_prop_impl              false
% 1.40/0.95  --prep_def_merge_mbd                    true
% 1.40/0.95  --prep_def_merge_tr_red                 false
% 1.40/0.95  --prep_def_merge_tr_cl                  false
% 1.40/0.95  --smt_preprocessing                     true
% 1.40/0.95  --smt_ac_axioms                         fast
% 1.40/0.95  --preprocessed_out                      false
% 1.40/0.95  --preprocessed_stats                    false
% 1.40/0.95  
% 1.40/0.95  ------ Abstraction refinement Options
% 1.40/0.95  
% 1.40/0.95  --abstr_ref                             []
% 1.40/0.95  --abstr_ref_prep                        false
% 1.40/0.95  --abstr_ref_until_sat                   false
% 1.40/0.95  --abstr_ref_sig_restrict                funpre
% 1.40/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.95  --abstr_ref_under                       []
% 1.40/0.95  
% 1.40/0.95  ------ SAT Options
% 1.40/0.95  
% 1.40/0.95  --sat_mode                              false
% 1.40/0.95  --sat_fm_restart_options                ""
% 1.40/0.95  --sat_gr_def                            false
% 1.40/0.95  --sat_epr_types                         true
% 1.40/0.95  --sat_non_cyclic_types                  false
% 1.40/0.95  --sat_finite_models                     false
% 1.40/0.95  --sat_fm_lemmas                         false
% 1.40/0.95  --sat_fm_prep                           false
% 1.40/0.95  --sat_fm_uc_incr                        true
% 1.40/0.95  --sat_out_model                         small
% 1.40/0.95  --sat_out_clauses                       false
% 1.40/0.95  
% 1.40/0.95  ------ QBF Options
% 1.40/0.95  
% 1.40/0.95  --qbf_mode                              false
% 1.40/0.95  --qbf_elim_univ                         false
% 1.40/0.95  --qbf_dom_inst                          none
% 1.40/0.95  --qbf_dom_pre_inst                      false
% 1.40/0.95  --qbf_sk_in                             false
% 1.40/0.95  --qbf_pred_elim                         true
% 1.40/0.95  --qbf_split                             512
% 1.40/0.95  
% 1.40/0.95  ------ BMC1 Options
% 1.40/0.95  
% 1.40/0.95  --bmc1_incremental                      false
% 1.40/0.95  --bmc1_axioms                           reachable_all
% 1.40/0.95  --bmc1_min_bound                        0
% 1.40/0.95  --bmc1_max_bound                        -1
% 1.40/0.95  --bmc1_max_bound_default                -1
% 1.40/0.95  --bmc1_symbol_reachability              true
% 1.40/0.95  --bmc1_property_lemmas                  false
% 1.40/0.95  --bmc1_k_induction                      false
% 1.40/0.95  --bmc1_non_equiv_states                 false
% 1.40/0.95  --bmc1_deadlock                         false
% 1.40/0.95  --bmc1_ucm                              false
% 1.40/0.95  --bmc1_add_unsat_core                   none
% 1.40/0.95  --bmc1_unsat_core_children              false
% 1.40/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.95  --bmc1_out_stat                         full
% 1.40/0.95  --bmc1_ground_init                      false
% 1.40/0.95  --bmc1_pre_inst_next_state              false
% 1.40/0.95  --bmc1_pre_inst_state                   false
% 1.40/0.95  --bmc1_pre_inst_reach_state             false
% 1.40/0.95  --bmc1_out_unsat_core                   false
% 1.40/0.95  --bmc1_aig_witness_out                  false
% 1.40/0.95  --bmc1_verbose                          false
% 1.40/0.95  --bmc1_dump_clauses_tptp                false
% 1.40/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.95  --bmc1_dump_file                        -
% 1.40/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.95  --bmc1_ucm_extend_mode                  1
% 1.40/0.95  --bmc1_ucm_init_mode                    2
% 1.40/0.95  --bmc1_ucm_cone_mode                    none
% 1.40/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.95  --bmc1_ucm_relax_model                  4
% 1.40/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.95  --bmc1_ucm_layered_model                none
% 1.40/0.95  --bmc1_ucm_max_lemma_size               10
% 1.40/0.95  
% 1.40/0.95  ------ AIG Options
% 1.40/0.95  
% 1.40/0.95  --aig_mode                              false
% 1.40/0.95  
% 1.40/0.95  ------ Instantiation Options
% 1.40/0.95  
% 1.40/0.95  --instantiation_flag                    true
% 1.40/0.95  --inst_sos_flag                         false
% 1.40/0.95  --inst_sos_phase                        true
% 1.40/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.95  --inst_lit_sel_side                     none
% 1.40/0.95  --inst_solver_per_active                1400
% 1.40/0.95  --inst_solver_calls_frac                1.
% 1.40/0.95  --inst_passive_queue_type               priority_queues
% 1.40/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.95  --inst_passive_queues_freq              [25;2]
% 1.40/0.95  --inst_dismatching                      true
% 1.40/0.95  --inst_eager_unprocessed_to_passive     true
% 1.40/0.95  --inst_prop_sim_given                   true
% 1.40/0.95  --inst_prop_sim_new                     false
% 1.40/0.95  --inst_subs_new                         false
% 1.40/0.95  --inst_eq_res_simp                      false
% 1.40/0.95  --inst_subs_given                       false
% 1.40/0.95  --inst_orphan_elimination               true
% 1.40/0.95  --inst_learning_loop_flag               true
% 1.40/0.95  --inst_learning_start                   3000
% 1.40/0.95  --inst_learning_factor                  2
% 1.40/0.95  --inst_start_prop_sim_after_learn       3
% 1.40/0.95  --inst_sel_renew                        solver
% 1.40/0.95  --inst_lit_activity_flag                true
% 1.40/0.95  --inst_restr_to_given                   false
% 1.40/0.95  --inst_activity_threshold               500
% 1.40/0.95  --inst_out_proof                        true
% 1.40/0.95  
% 1.40/0.95  ------ Resolution Options
% 1.40/0.95  
% 1.40/0.95  --resolution_flag                       false
% 1.40/0.95  --res_lit_sel                           adaptive
% 1.40/0.95  --res_lit_sel_side                      none
% 1.40/0.95  --res_ordering                          kbo
% 1.40/0.95  --res_to_prop_solver                    active
% 1.40/0.95  --res_prop_simpl_new                    false
% 1.40/0.95  --res_prop_simpl_given                  true
% 1.40/0.95  --res_passive_queue_type                priority_queues
% 1.40/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.95  --res_passive_queues_freq               [15;5]
% 1.40/0.95  --res_forward_subs                      full
% 1.40/0.95  --res_backward_subs                     full
% 1.40/0.95  --res_forward_subs_resolution           true
% 1.40/0.95  --res_backward_subs_resolution          true
% 1.40/0.95  --res_orphan_elimination                true
% 1.40/0.95  --res_time_limit                        2.
% 1.40/0.95  --res_out_proof                         true
% 1.40/0.95  
% 1.40/0.95  ------ Superposition Options
% 1.40/0.95  
% 1.40/0.95  --superposition_flag                    true
% 1.40/0.95  --sup_passive_queue_type                priority_queues
% 1.40/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.95  --demod_completeness_check              fast
% 1.40/0.95  --demod_use_ground                      true
% 1.40/0.95  --sup_to_prop_solver                    passive
% 1.40/0.95  --sup_prop_simpl_new                    true
% 1.40/0.95  --sup_prop_simpl_given                  true
% 1.40/0.95  --sup_fun_splitting                     false
% 1.40/0.95  --sup_smt_interval                      50000
% 1.40/0.95  
% 1.40/0.95  ------ Superposition Simplification Setup
% 1.40/0.95  
% 1.40/0.95  --sup_indices_passive                   []
% 1.40/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_full_bw                           [BwDemod]
% 1.40/0.95  --sup_immed_triv                        [TrivRules]
% 1.40/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_immed_bw_main                     []
% 1.40/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.95  
% 1.40/0.95  ------ Combination Options
% 1.40/0.95  
% 1.40/0.95  --comb_res_mult                         3
% 1.40/0.95  --comb_sup_mult                         2
% 1.40/0.95  --comb_inst_mult                        10
% 1.40/0.95  
% 1.40/0.95  ------ Debug Options
% 1.40/0.95  
% 1.40/0.95  --dbg_backtrace                         false
% 1.40/0.95  --dbg_dump_prop_clauses                 false
% 1.40/0.95  --dbg_dump_prop_clauses_file            -
% 1.40/0.95  --dbg_out_stat                          false
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  ------ Proving...
% 1.40/0.95  
% 1.40/0.95  
% 1.40/0.95  % SZS status Theorem for theBenchmark.p
% 1.40/0.95  
% 1.40/0.95   Resolution empty clause
% 1.40/0.95  
% 1.40/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.40/0.95  
% 1.40/0.95  fof(f4,axiom,(
% 1.40/0.95    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f39,plain,(
% 1.40/0.95    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.95    inference(cnf_transformation,[],[f4])).
% 1.40/0.95  
% 1.40/0.95  fof(f11,axiom,(
% 1.40/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f17,plain,(
% 1.40/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.40/0.95    inference(pure_predicate_removal,[],[f11])).
% 1.40/0.95  
% 1.40/0.95  fof(f25,plain,(
% 1.40/0.95    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.95    inference(ennf_transformation,[],[f17])).
% 1.40/0.95  
% 1.40/0.95  fof(f47,plain,(
% 1.40/0.95    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.95    inference(cnf_transformation,[],[f25])).
% 1.40/0.95  
% 1.40/0.95  fof(f9,axiom,(
% 1.40/0.95    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f23,plain,(
% 1.40/0.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.95    inference(ennf_transformation,[],[f9])).
% 1.40/0.95  
% 1.40/0.95  fof(f24,plain,(
% 1.40/0.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.95    inference(flattening,[],[f23])).
% 1.40/0.95  
% 1.40/0.95  fof(f44,plain,(
% 1.40/0.95    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.95    inference(cnf_transformation,[],[f24])).
% 1.40/0.95  
% 1.40/0.95  fof(f3,axiom,(
% 1.40/0.95    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f30,plain,(
% 1.40/0.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.40/0.95    inference(nnf_transformation,[],[f3])).
% 1.40/0.95  
% 1.40/0.95  fof(f31,plain,(
% 1.40/0.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.40/0.95    inference(flattening,[],[f30])).
% 1.40/0.95  
% 1.40/0.95  fof(f38,plain,(
% 1.40/0.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.40/0.95    inference(cnf_transformation,[],[f31])).
% 1.40/0.95  
% 1.40/0.95  fof(f51,plain,(
% 1.40/0.95    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.40/0.95    inference(equality_resolution,[],[f38])).
% 1.40/0.95  
% 1.40/0.95  fof(f7,axiom,(
% 1.40/0.95    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f42,plain,(
% 1.40/0.95    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.40/0.95    inference(cnf_transformation,[],[f7])).
% 1.40/0.95  
% 1.40/0.95  fof(f8,axiom,(
% 1.40/0.95    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f22,plain,(
% 1.40/0.95    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.95    inference(ennf_transformation,[],[f8])).
% 1.40/0.95  
% 1.40/0.95  fof(f43,plain,(
% 1.40/0.95    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.95    inference(cnf_transformation,[],[f22])).
% 1.40/0.95  
% 1.40/0.95  fof(f10,axiom,(
% 1.40/0.95    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f46,plain,(
% 1.40/0.95    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.95    inference(cnf_transformation,[],[f10])).
% 1.40/0.95  
% 1.40/0.95  fof(f12,axiom,(
% 1.40/0.95    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f26,plain,(
% 1.40/0.95    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.95    inference(ennf_transformation,[],[f12])).
% 1.40/0.95  
% 1.40/0.95  fof(f48,plain,(
% 1.40/0.95    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.95    inference(cnf_transformation,[],[f26])).
% 1.40/0.95  
% 1.40/0.95  fof(f13,conjecture,(
% 1.40/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f14,negated_conjecture,(
% 1.40/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.40/0.95    inference(negated_conjecture,[],[f13])).
% 1.40/0.95  
% 1.40/0.95  fof(f15,plain,(
% 1.40/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.40/0.95    inference(pure_predicate_removal,[],[f14])).
% 1.40/0.95  
% 1.40/0.95  fof(f16,plain,(
% 1.40/0.95    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.40/0.95    inference(pure_predicate_removal,[],[f15])).
% 1.40/0.95  
% 1.40/0.95  fof(f27,plain,(
% 1.40/0.95    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 1.40/0.95    inference(ennf_transformation,[],[f16])).
% 1.40/0.95  
% 1.40/0.95  fof(f32,plain,(
% 1.40/0.95    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))))),
% 1.40/0.95    introduced(choice_axiom,[])).
% 1.40/0.95  
% 1.40/0.95  fof(f33,plain,(
% 1.40/0.95    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.40/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32])).
% 1.40/0.95  
% 1.40/0.95  fof(f49,plain,(
% 1.40/0.95    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.40/0.95    inference(cnf_transformation,[],[f33])).
% 1.40/0.95  
% 1.40/0.95  fof(f37,plain,(
% 1.40/0.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.40/0.95    inference(cnf_transformation,[],[f31])).
% 1.40/0.95  
% 1.40/0.95  fof(f52,plain,(
% 1.40/0.95    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.40/0.95    inference(equality_resolution,[],[f37])).
% 1.40/0.95  
% 1.40/0.95  fof(f2,axiom,(
% 1.40/0.95    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f18,plain,(
% 1.40/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.40/0.95    inference(ennf_transformation,[],[f2])).
% 1.40/0.95  
% 1.40/0.95  fof(f28,plain,(
% 1.40/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.40/0.95    introduced(choice_axiom,[])).
% 1.40/0.95  
% 1.40/0.95  fof(f29,plain,(
% 1.40/0.95    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.40/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).
% 1.40/0.95  
% 1.40/0.95  fof(f35,plain,(
% 1.40/0.95    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.40/0.95    inference(cnf_transformation,[],[f29])).
% 1.40/0.95  
% 1.40/0.95  fof(f1,axiom,(
% 1.40/0.95    v1_xboole_0(k1_xboole_0)),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f34,plain,(
% 1.40/0.95    v1_xboole_0(k1_xboole_0)),
% 1.40/0.95    inference(cnf_transformation,[],[f1])).
% 1.40/0.95  
% 1.40/0.95  fof(f6,axiom,(
% 1.40/0.95    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.40/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.95  
% 1.40/0.95  fof(f21,plain,(
% 1.40/0.95    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.40/0.95    inference(ennf_transformation,[],[f6])).
% 1.40/0.95  
% 1.40/0.95  fof(f41,plain,(
% 1.40/0.95    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.40/0.95    inference(cnf_transformation,[],[f21])).
% 1.40/0.95  
% 1.40/0.95  fof(f50,plain,(
% 1.40/0.95    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2)),
% 1.40/0.95    inference(cnf_transformation,[],[f33])).
% 1.40/0.95  
% 1.40/0.95  cnf(c_5,plain,
% 1.40/0.95      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.40/0.95      inference(cnf_transformation,[],[f39]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_498,plain,
% 1.40/0.95      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_13,plain,
% 1.40/0.95      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.40/0.95      inference(cnf_transformation,[],[f47]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_10,plain,
% 1.40/0.95      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.40/0.95      inference(cnf_transformation,[],[f44]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_177,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.40/0.95      | ~ v1_relat_1(X0)
% 1.40/0.95      | k7_relat_1(X0,X1) = X0 ),
% 1.40/0.95      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_493,plain,
% 1.40/0.95      ( k7_relat_1(X0,X1) = X0
% 1.40/0.95      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.40/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1390,plain,
% 1.40/0.95      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 1.40/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.40/0.95      inference(superposition,[status(thm)],[c_498,c_493]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_2,plain,
% 1.40/0.95      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.40/0.95      inference(cnf_transformation,[],[f51]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_8,plain,
% 1.40/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.40/0.95      inference(cnf_transformation,[],[f42]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_497,plain,
% 1.40/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_699,plain,
% 1.40/0.95      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.40/0.95      inference(superposition,[status(thm)],[c_2,c_497]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1441,plain,
% 1.40/0.95      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.40/0.95      inference(global_propositional_subsumption,[status(thm)],[c_1390,c_699]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_9,plain,
% 1.40/0.95      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.40/0.95      inference(cnf_transformation,[],[f43]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_496,plain,
% 1.40/0.95      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 1.40/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_830,plain,
% 1.40/0.95      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 1.40/0.95      inference(superposition,[status(thm)],[c_699,c_496]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1445,plain,
% 1.40/0.95      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 1.40/0.95      inference(demodulation,[status(thm)],[c_1441,c_830]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_11,plain,
% 1.40/0.95      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.40/0.95      inference(cnf_transformation,[],[f46]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1446,plain,
% 1.40/0.95      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.40/0.95      inference(light_normalisation,[status(thm)],[c_1445,c_11]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_14,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.40/0.95      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.40/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_495,plain,
% 1.40/0.95      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.40/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1078,plain,
% 1.40/0.95      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 1.40/0.95      inference(superposition,[status(thm)],[c_498,c_495]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_16,negated_conjecture,
% 1.40/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
% 1.40/0.95      inference(cnf_transformation,[],[f49]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_494,plain,
% 1.40/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_3,plain,
% 1.40/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.40/0.95      inference(cnf_transformation,[],[f52]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_511,plain,
% 1.40/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.40/0.95      inference(demodulation,[status(thm)],[c_494,c_3]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_1,plain,
% 1.40/0.95      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.40/0.95      inference(cnf_transformation,[],[f35]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_0,plain,
% 1.40/0.95      ( v1_xboole_0(k1_xboole_0) ),
% 1.40/0.95      inference(cnf_transformation,[],[f34]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_7,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.40/0.95      | ~ r2_hidden(X2,X0)
% 1.40/0.95      | ~ v1_xboole_0(X1) ),
% 1.40/0.95      inference(cnf_transformation,[],[f41]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_141,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.40/0.95      | ~ r2_hidden(X2,X0)
% 1.40/0.95      | k1_xboole_0 != X1 ),
% 1.40/0.95      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_142,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 1.40/0.95      inference(unflattening,[status(thm)],[c_141]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_230,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.40/0.95      | X0 != X1
% 1.40/0.95      | sK0(X1) != X2
% 1.40/0.95      | k1_xboole_0 = X1 ),
% 1.40/0.95      inference(resolution_lifted,[status(thm)],[c_1,c_142]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_231,plain,
% 1.40/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 1.40/0.95      inference(unflattening,[status(thm)],[c_230]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_491,plain,
% 1.40/0.95      ( k1_xboole_0 = X0
% 1.40/0.95      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.40/0.95      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 1.40/0.95  
% 1.40/0.95  cnf(c_796,plain,
% 1.40/0.95      ( sK3 = k1_xboole_0 ),
% 1.40/0.96      inference(superposition,[status(thm)],[c_511,c_491]) ).
% 1.40/0.96  
% 1.40/0.96  cnf(c_15,negated_conjecture,
% 1.40/0.96      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
% 1.40/0.96      inference(cnf_transformation,[],[f50]) ).
% 1.40/0.96  
% 1.40/0.96  cnf(c_942,plain,
% 1.40/0.96      ( k7_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.40/0.96      inference(demodulation,[status(thm)],[c_796,c_15]) ).
% 1.40/0.96  
% 1.40/0.96  cnf(c_1095,plain,
% 1.40/0.96      ( k9_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.40/0.96      inference(demodulation,[status(thm)],[c_1078,c_942]) ).
% 1.40/0.96  
% 1.40/0.96  cnf(c_1450,plain,
% 1.40/0.96      ( k1_xboole_0 != k1_xboole_0 ),
% 1.40/0.96      inference(demodulation,[status(thm)],[c_1446,c_1095]) ).
% 1.40/0.96  
% 1.40/0.96  cnf(c_1451,plain,
% 1.40/0.96      ( $false ),
% 1.40/0.96      inference(equality_resolution_simp,[status(thm)],[c_1450]) ).
% 1.40/0.96  
% 1.40/0.96  
% 1.40/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.40/0.96  
% 1.40/0.96  ------                               Statistics
% 1.40/0.96  
% 1.40/0.96  ------ General
% 1.40/0.96  
% 1.40/0.96  abstr_ref_over_cycles:                  0
% 1.40/0.96  abstr_ref_under_cycles:                 0
% 1.40/0.96  gc_basic_clause_elim:                   0
% 1.40/0.96  forced_gc_time:                         0
% 1.40/0.96  parsing_time:                           0.01
% 1.40/0.96  unif_index_cands_time:                  0.
% 1.40/0.96  unif_index_add_time:                    0.
% 1.40/0.96  orderings_time:                         0.
% 1.40/0.96  out_proof_time:                         0.01
% 1.40/0.96  total_time:                             0.085
% 1.40/0.96  num_of_symbols:                         48
% 1.40/0.96  num_of_terms:                           1573
% 1.40/0.96  
% 1.40/0.96  ------ Preprocessing
% 1.40/0.96  
% 1.40/0.96  num_of_splits:                          0
% 1.40/0.96  num_of_split_atoms:                     0
% 1.40/0.96  num_of_reused_defs:                     0
% 1.40/0.96  num_eq_ax_congr_red:                    18
% 1.40/0.96  num_of_sem_filtered_clauses:            1
% 1.40/0.96  num_of_subtypes:                        0
% 1.40/0.96  monotx_restored_types:                  0
% 1.40/0.96  sat_num_of_epr_types:                   0
% 1.40/0.96  sat_num_of_non_cyclic_types:            0
% 1.40/0.96  sat_guarded_non_collapsed_types:        0
% 1.40/0.96  num_pure_diseq_elim:                    0
% 1.40/0.96  simp_replaced_by:                       0
% 1.40/0.96  res_preprocessed:                       78
% 1.40/0.96  prep_upred:                             0
% 1.40/0.96  prep_unflattend:                        11
% 1.40/0.96  smt_new_axioms:                         0
% 1.40/0.96  pred_elim_cands:                        2
% 1.40/0.96  pred_elim:                              3
% 1.40/0.96  pred_elim_cl:                           3
% 1.40/0.96  pred_elim_cycles:                       7
% 1.40/0.96  merged_defs:                            0
% 1.40/0.96  merged_defs_ncl:                        0
% 1.40/0.96  bin_hyper_res:                          0
% 1.40/0.96  prep_cycles:                            4
% 1.40/0.96  pred_elim_time:                         0.003
% 1.40/0.96  splitting_time:                         0.
% 1.40/0.96  sem_filter_time:                        0.
% 1.40/0.96  monotx_time:                            0.001
% 1.40/0.96  subtype_inf_time:                       0.
% 1.40/0.96  
% 1.40/0.96  ------ Problem properties
% 1.40/0.96  
% 1.40/0.96  clauses:                                14
% 1.40/0.96  conjectures:                            2
% 1.40/0.96  epr:                                    0
% 1.40/0.96  horn:                                   12
% 1.40/0.96  ground:                                 4
% 1.40/0.96  unary:                                  8
% 1.40/0.96  binary:                                 3
% 1.40/0.96  lits:                                   23
% 1.40/0.96  lits_eq:                                13
% 1.40/0.96  fd_pure:                                0
% 1.40/0.96  fd_pseudo:                              0
% 1.40/0.96  fd_cond:                                3
% 1.40/0.96  fd_pseudo_cond:                         0
% 1.40/0.96  ac_symbols:                             0
% 1.40/0.96  
% 1.40/0.96  ------ Propositional Solver
% 1.40/0.96  
% 1.40/0.96  prop_solver_calls:                      27
% 1.40/0.96  prop_fast_solver_calls:                 358
% 1.40/0.96  smt_solver_calls:                       0
% 1.40/0.96  smt_fast_solver_calls:                  0
% 1.40/0.96  prop_num_of_clauses:                    522
% 1.40/0.96  prop_preprocess_simplified:             2599
% 1.40/0.96  prop_fo_subsumed:                       1
% 1.40/0.96  prop_solver_time:                       0.
% 1.40/0.96  smt_solver_time:                        0.
% 1.40/0.96  smt_fast_solver_time:                   0.
% 1.40/0.96  prop_fast_solver_time:                  0.
% 1.40/0.96  prop_unsat_core_time:                   0.
% 1.40/0.96  
% 1.40/0.96  ------ QBF
% 1.40/0.96  
% 1.40/0.96  qbf_q_res:                              0
% 1.40/0.96  qbf_num_tautologies:                    0
% 1.40/0.96  qbf_prep_cycles:                        0
% 1.40/0.96  
% 1.40/0.96  ------ BMC1
% 1.40/0.96  
% 1.40/0.96  bmc1_current_bound:                     -1
% 1.40/0.96  bmc1_last_solved_bound:                 -1
% 1.40/0.96  bmc1_unsat_core_size:                   -1
% 1.40/0.96  bmc1_unsat_core_parents_size:           -1
% 1.40/0.96  bmc1_merge_next_fun:                    0
% 1.40/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.40/0.96  
% 1.40/0.96  ------ Instantiation
% 1.40/0.96  
% 1.40/0.96  inst_num_of_clauses:                    244
% 1.40/0.96  inst_num_in_passive:                    95
% 1.40/0.96  inst_num_in_active:                     122
% 1.40/0.96  inst_num_in_unprocessed:                27
% 1.40/0.96  inst_num_of_loops:                      130
% 1.40/0.96  inst_num_of_learning_restarts:          0
% 1.40/0.96  inst_num_moves_active_passive:          6
% 1.40/0.96  inst_lit_activity:                      0
% 1.40/0.96  inst_lit_activity_moves:                0
% 1.40/0.96  inst_num_tautologies:                   0
% 1.40/0.96  inst_num_prop_implied:                  0
% 1.40/0.96  inst_num_existing_simplified:           0
% 1.40/0.96  inst_num_eq_res_simplified:             0
% 1.40/0.96  inst_num_child_elim:                    0
% 1.40/0.96  inst_num_of_dismatching_blockings:      32
% 1.40/0.96  inst_num_of_non_proper_insts:           166
% 1.40/0.96  inst_num_of_duplicates:                 0
% 1.40/0.96  inst_inst_num_from_inst_to_res:         0
% 1.40/0.96  inst_dismatching_checking_time:         0.
% 1.40/0.96  
% 1.40/0.96  ------ Resolution
% 1.40/0.96  
% 1.40/0.96  res_num_of_clauses:                     0
% 1.40/0.96  res_num_in_passive:                     0
% 1.40/0.96  res_num_in_active:                      0
% 1.40/0.96  res_num_of_loops:                       82
% 1.40/0.96  res_forward_subset_subsumed:            13
% 1.40/0.96  res_backward_subset_subsumed:           0
% 1.40/0.96  res_forward_subsumed:                   0
% 1.40/0.96  res_backward_subsumed:                  0
% 1.40/0.96  res_forward_subsumption_resolution:     0
% 1.40/0.96  res_backward_subsumption_resolution:    0
% 1.40/0.96  res_clause_to_clause_subsumption:       37
% 1.40/0.96  res_orphan_elimination:                 0
% 1.40/0.96  res_tautology_del:                      12
% 1.40/0.96  res_num_eq_res_simplified:              0
% 1.40/0.96  res_num_sel_changes:                    0
% 1.40/0.96  res_moves_from_active_to_pass:          0
% 1.40/0.96  
% 1.40/0.96  ------ Superposition
% 1.40/0.96  
% 1.40/0.96  sup_time_total:                         0.
% 1.40/0.96  sup_time_generating:                    0.
% 1.40/0.96  sup_time_sim_full:                      0.
% 1.40/0.96  sup_time_sim_immed:                     0.
% 1.40/0.96  
% 1.40/0.96  sup_num_of_clauses:                     22
% 1.40/0.96  sup_num_in_active:                      19
% 1.40/0.96  sup_num_in_passive:                     3
% 1.40/0.96  sup_num_of_loops:                       25
% 1.40/0.96  sup_fw_superposition:                   19
% 1.40/0.96  sup_bw_superposition:                   1
% 1.40/0.96  sup_immediate_simplified:               8
% 1.40/0.96  sup_given_eliminated:                   0
% 1.40/0.96  comparisons_done:                       0
% 1.40/0.96  comparisons_avoided:                    0
% 1.40/0.96  
% 1.40/0.96  ------ Simplifications
% 1.40/0.96  
% 1.40/0.96  
% 1.40/0.96  sim_fw_subset_subsumed:                 1
% 1.40/0.96  sim_bw_subset_subsumed:                 0
% 1.40/0.96  sim_fw_subsumed:                        3
% 1.40/0.96  sim_bw_subsumed:                        1
% 1.40/0.96  sim_fw_subsumption_res:                 0
% 1.40/0.96  sim_bw_subsumption_res:                 0
% 1.40/0.96  sim_tautology_del:                      0
% 1.40/0.96  sim_eq_tautology_del:                   2
% 1.40/0.96  sim_eq_res_simp:                        0
% 1.40/0.96  sim_fw_demodulated:                     1
% 1.40/0.96  sim_bw_demodulated:                     6
% 1.40/0.96  sim_light_normalised:                   3
% 1.40/0.96  sim_joinable_taut:                      0
% 1.40/0.96  sim_joinable_simp:                      0
% 1.40/0.96  sim_ac_normalised:                      0
% 1.40/0.96  sim_smt_subsumption:                    0
% 1.40/0.96  
%------------------------------------------------------------------------------
