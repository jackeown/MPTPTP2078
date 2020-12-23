%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1002+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:37 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  115 (1044 expanded)
%              Number of clauses        :   80 ( 412 expanded)
%              Number of leaves         :   12 ( 179 expanded)
%              Depth                    :   22
%              Number of atoms          :  326 (4419 expanded)
%              Number of equality atoms :  198 (1687 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f25])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_219,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_220,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_396,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | sK1 != X1
    | sK0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_220])).

cnf(c_397,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_453,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_397])).

cnf(c_481,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_210,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_211,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_485,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_45,X1_45,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_706,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_485])).

cnf(c_800,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_481,c_706])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_255,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_256,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_369,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_256])).

cnf(c_370,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_484,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK3,k9_relat_1(sK3,X0_48)))
    | ~ r1_tarski(X0_48,k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_493,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_484])).

cnf(c_530,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_492,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK3,k9_relat_1(sK3,X0_48)))
    | ~ r1_tarski(X0_48,k1_relat_1(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_484])).

cnf(c_531,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK3,k9_relat_1(sK3,X0_48))) = iProver_top
    | r1_tarski(X0_48,k1_relat_1(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_533,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_496,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_691,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_510,plain,
    ( ~ r1_tarski(X0_48,X0_45)
    | r1_tarski(X0_48,X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_707,plain,
    ( r1_tarski(sK2,X0_45)
    | ~ r1_tarski(sK2,sK0)
    | X0_45 != sK0 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_715,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,sK0)
    | k1_relat_1(sK3) != sK0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_717,plain,
    ( k1_relat_1(sK3) != sK0
    | r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_491,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_484])).

cnf(c_853,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_854,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_192,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_193,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_487,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k8_relset_1(X0_45,X1_45,sK3,X0_49) = k10_relat_1(sK3,X0_49) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_727,plain,
    ( k8_relset_1(sK0,sK1,sK3,X0_49) = k10_relat_1(sK3,X0_49) ),
    inference(equality_resolution,[status(thm)],[c_487])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_201,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_202,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_486,plain,
    ( k7_relset_1(X0_45,X1_45,sK3,X0_48) = k9_relat_1(sK3,X0_48)
    | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_723,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0_48) = k9_relat_1(sK3,X0_48) ),
    inference(equality_resolution,[status(thm)],[c_486])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_490,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_619,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_845,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_723,c_619])).

cnf(c_878,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_727,c_845])).

cnf(c_975,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_18,c_530,c_533,c_691,c_717,c_854,c_878])).

cnf(c_980,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_975,c_706])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_489,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_987,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_975,c_489])).

cnf(c_988,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_987])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_302,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_303,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_421,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | sK1 != X0
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_303])).

cnf(c_422,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_482,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_983,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_975,c_482])).

cnf(c_1006,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_983,c_988])).

cnf(c_1007,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1006])).

cnf(c_1011,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_980,c_988,c_1007])).

cnf(c_499,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_791,plain,
    ( X0_45 != X1_45
    | X0_45 = sK1
    | sK1 != X1_45 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_792,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_777,plain,
    ( k1_relat_1(sK3) != X0_45
    | k1_relat_1(sK3) = sK0
    | sK0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_778,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_495,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_733,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_699,plain,
    ( sK0 != X0_45
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_732,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_521,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1011,c_878,c_854,c_800,c_792,c_778,c_733,c_732,c_717,c_691,c_533,c_530,c_489,c_521,c_18])).


%------------------------------------------------------------------------------
