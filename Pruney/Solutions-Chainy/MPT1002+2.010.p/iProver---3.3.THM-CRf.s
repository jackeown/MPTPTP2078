%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:24 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 196 expanded)
%              Number of clauses        :   72 (  79 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 ( 829 expanded)
%              Number of equality atoms :  156 ( 317 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,
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

fof(f27,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_218,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_219,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_392,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | sK1 != X1
    | sK0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_219])).

cnf(c_393,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_453,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_393])).

cnf(c_502,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_272,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_273,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_505,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_45,X1_45,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_273])).

cnf(c_791,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_505])).

cnf(c_1060,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_502,c_791])).

cnf(c_4,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_512,plain,
    ( r1_tarski(X0_45,k10_relat_1(X1_45,k9_relat_1(X1_45,X0_45)))
    | ~ r1_tarski(X0_45,k1_relat_1(X1_45))
    | ~ v1_relat_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_679,plain,
    ( r1_tarski(X0_45,k10_relat_1(X1_45,k9_relat_1(X1_45,X0_45))) = iProver_top
    | r1_tarski(X0_45,k1_relat_1(X1_45)) != iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_263,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_264,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_506,plain,
    ( k7_relset_1(X0_45,X1_45,sK3,X2_45) = k9_relat_1(sK3,X2_45)
    | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_264])).

cnf(c_806,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0_45) = k9_relat_1(sK3,X0_45) ),
    inference(equality_resolution,[status(thm)],[c_506])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_511,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_680,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1161,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_806,c_680])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_254,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_255,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_507,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k8_relset_1(X0_45,X1_45,sK3,X0_47) = k10_relat_1(sK3,X0_47) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_810,plain,
    ( k8_relset_1(sK0,sK1,sK3,X0_47) = k10_relat_1(sK3,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_507])).

cnf(c_1223,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1161,c_810])).

cnf(c_1226,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_1223])).

cnf(c_518,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_768,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_203,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_204,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_508,plain,
    ( ~ v1_relat_1(X0_45)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_763,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_45,X1_45))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_842,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_843,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_513,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_954,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_955,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_1327,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1226,c_768,c_843,c_955])).

cnf(c_1332,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1327])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_514,plain,
    ( r1_tarski(k1_xboole_0,X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1287,plain,
    ( r1_tarski(k1_xboole_0,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_523,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | r1_tarski(X2_45,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_818,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | r1_tarski(sK2,X2_45)
    | X2_45 != X1_45
    | sK2 != X0_45 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_925,plain,
    ( ~ r1_tarski(sK2,X0_45)
    | r1_tarski(sK2,X1_45)
    | X1_45 != X0_45
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1172,plain,
    ( r1_tarski(sK2,X0_45)
    | ~ r1_tarski(sK2,sK0)
    | X0_45 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_1174,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_520,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_974,plain,
    ( X0_45 != X1_45
    | X0_45 = sK1
    | sK1 != X1_45 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_975,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_517,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_824,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_515,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | ~ r1_tarski(X2_45,X0_45)
    | r1_tarski(X2_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_781,plain,
    ( ~ r1_tarski(X0_45,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | ~ r1_tarski(sK2,X0_45)
    | r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_783,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_510,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_544,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1332,c_1287,c_1174,c_975,c_824,c_783,c_510,c_544,c_14,c_21,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.69/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/0.97  
% 1.69/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.69/0.97  
% 1.69/0.97  ------  iProver source info
% 1.69/0.97  
% 1.69/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.69/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.69/0.97  git: non_committed_changes: false
% 1.69/0.97  git: last_make_outside_of_git: false
% 1.69/0.97  
% 1.69/0.97  ------ 
% 1.69/0.97  
% 1.69/0.97  ------ Input Options
% 1.69/0.97  
% 1.69/0.97  --out_options                           all
% 1.69/0.97  --tptp_safe_out                         true
% 1.69/0.97  --problem_path                          ""
% 1.69/0.97  --include_path                          ""
% 1.69/0.97  --clausifier                            res/vclausify_rel
% 1.69/0.97  --clausifier_options                    --mode clausify
% 1.69/0.97  --stdin                                 false
% 1.69/0.97  --stats_out                             all
% 1.69/0.97  
% 1.69/0.97  ------ General Options
% 1.69/0.97  
% 1.69/0.97  --fof                                   false
% 1.69/0.97  --time_out_real                         305.
% 1.69/0.97  --time_out_virtual                      -1.
% 1.69/0.97  --symbol_type_check                     false
% 1.69/0.97  --clausify_out                          false
% 1.69/0.97  --sig_cnt_out                           false
% 1.69/0.97  --trig_cnt_out                          false
% 1.69/0.97  --trig_cnt_out_tolerance                1.
% 1.69/0.97  --trig_cnt_out_sk_spl                   false
% 1.69/0.97  --abstr_cl_out                          false
% 1.69/0.97  
% 1.69/0.97  ------ Global Options
% 1.69/0.97  
% 1.69/0.97  --schedule                              default
% 1.69/0.97  --add_important_lit                     false
% 1.69/0.97  --prop_solver_per_cl                    1000
% 1.69/0.97  --min_unsat_core                        false
% 1.69/0.97  --soft_assumptions                      false
% 1.69/0.97  --soft_lemma_size                       3
% 1.69/0.97  --prop_impl_unit_size                   0
% 1.69/0.97  --prop_impl_unit                        []
% 1.69/0.97  --share_sel_clauses                     true
% 1.69/0.97  --reset_solvers                         false
% 1.69/0.97  --bc_imp_inh                            [conj_cone]
% 1.69/0.97  --conj_cone_tolerance                   3.
% 1.69/0.97  --extra_neg_conj                        none
% 1.69/0.97  --large_theory_mode                     true
% 1.69/0.97  --prolific_symb_bound                   200
% 1.69/0.97  --lt_threshold                          2000
% 1.69/0.97  --clause_weak_htbl                      true
% 1.69/0.97  --gc_record_bc_elim                     false
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing Options
% 1.69/0.97  
% 1.69/0.97  --preprocessing_flag                    true
% 1.69/0.97  --time_out_prep_mult                    0.1
% 1.69/0.97  --splitting_mode                        input
% 1.69/0.97  --splitting_grd                         true
% 1.69/0.97  --splitting_cvd                         false
% 1.69/0.97  --splitting_cvd_svl                     false
% 1.69/0.97  --splitting_nvd                         32
% 1.69/0.97  --sub_typing                            true
% 1.69/0.97  --prep_gs_sim                           true
% 1.69/0.97  --prep_unflatten                        true
% 1.69/0.97  --prep_res_sim                          true
% 1.69/0.97  --prep_upred                            true
% 1.69/0.97  --prep_sem_filter                       exhaustive
% 1.69/0.97  --prep_sem_filter_out                   false
% 1.69/0.97  --pred_elim                             true
% 1.69/0.97  --res_sim_input                         true
% 1.69/0.97  --eq_ax_congr_red                       true
% 1.69/0.97  --pure_diseq_elim                       true
% 1.69/0.97  --brand_transform                       false
% 1.69/0.97  --non_eq_to_eq                          false
% 1.69/0.97  --prep_def_merge                        true
% 1.69/0.97  --prep_def_merge_prop_impl              false
% 1.69/0.97  --prep_def_merge_mbd                    true
% 1.69/0.97  --prep_def_merge_tr_red                 false
% 1.69/0.97  --prep_def_merge_tr_cl                  false
% 1.69/0.97  --smt_preprocessing                     true
% 1.69/0.97  --smt_ac_axioms                         fast
% 1.69/0.97  --preprocessed_out                      false
% 1.69/0.97  --preprocessed_stats                    false
% 1.69/0.97  
% 1.69/0.97  ------ Abstraction refinement Options
% 1.69/0.97  
% 1.69/0.97  --abstr_ref                             []
% 1.69/0.97  --abstr_ref_prep                        false
% 1.69/0.97  --abstr_ref_until_sat                   false
% 1.69/0.97  --abstr_ref_sig_restrict                funpre
% 1.69/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.97  --abstr_ref_under                       []
% 1.69/0.97  
% 1.69/0.97  ------ SAT Options
% 1.69/0.97  
% 1.69/0.97  --sat_mode                              false
% 1.69/0.97  --sat_fm_restart_options                ""
% 1.69/0.97  --sat_gr_def                            false
% 1.69/0.97  --sat_epr_types                         true
% 1.69/0.97  --sat_non_cyclic_types                  false
% 1.69/0.97  --sat_finite_models                     false
% 1.69/0.97  --sat_fm_lemmas                         false
% 1.69/0.97  --sat_fm_prep                           false
% 1.69/0.97  --sat_fm_uc_incr                        true
% 1.69/0.97  --sat_out_model                         small
% 1.69/0.97  --sat_out_clauses                       false
% 1.69/0.97  
% 1.69/0.97  ------ QBF Options
% 1.69/0.97  
% 1.69/0.97  --qbf_mode                              false
% 1.69/0.97  --qbf_elim_univ                         false
% 1.69/0.97  --qbf_dom_inst                          none
% 1.69/0.97  --qbf_dom_pre_inst                      false
% 1.69/0.97  --qbf_sk_in                             false
% 1.69/0.97  --qbf_pred_elim                         true
% 1.69/0.97  --qbf_split                             512
% 1.69/0.97  
% 1.69/0.97  ------ BMC1 Options
% 1.69/0.97  
% 1.69/0.97  --bmc1_incremental                      false
% 1.69/0.97  --bmc1_axioms                           reachable_all
% 1.69/0.97  --bmc1_min_bound                        0
% 1.69/0.97  --bmc1_max_bound                        -1
% 1.69/0.97  --bmc1_max_bound_default                -1
% 1.69/0.97  --bmc1_symbol_reachability              true
% 1.69/0.97  --bmc1_property_lemmas                  false
% 1.69/0.97  --bmc1_k_induction                      false
% 1.69/0.97  --bmc1_non_equiv_states                 false
% 1.69/0.97  --bmc1_deadlock                         false
% 1.69/0.97  --bmc1_ucm                              false
% 1.69/0.97  --bmc1_add_unsat_core                   none
% 1.69/0.97  --bmc1_unsat_core_children              false
% 1.69/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.97  --bmc1_out_stat                         full
% 1.69/0.97  --bmc1_ground_init                      false
% 1.69/0.97  --bmc1_pre_inst_next_state              false
% 1.69/0.97  --bmc1_pre_inst_state                   false
% 1.69/0.97  --bmc1_pre_inst_reach_state             false
% 1.69/0.97  --bmc1_out_unsat_core                   false
% 1.69/0.97  --bmc1_aig_witness_out                  false
% 1.69/0.97  --bmc1_verbose                          false
% 1.69/0.97  --bmc1_dump_clauses_tptp                false
% 1.69/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.97  --bmc1_dump_file                        -
% 1.69/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.97  --bmc1_ucm_extend_mode                  1
% 1.69/0.97  --bmc1_ucm_init_mode                    2
% 1.69/0.97  --bmc1_ucm_cone_mode                    none
% 1.69/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.97  --bmc1_ucm_relax_model                  4
% 1.69/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.97  --bmc1_ucm_layered_model                none
% 1.69/0.97  --bmc1_ucm_max_lemma_size               10
% 1.69/0.97  
% 1.69/0.97  ------ AIG Options
% 1.69/0.97  
% 1.69/0.97  --aig_mode                              false
% 1.69/0.97  
% 1.69/0.97  ------ Instantiation Options
% 1.69/0.97  
% 1.69/0.97  --instantiation_flag                    true
% 1.69/0.97  --inst_sos_flag                         false
% 1.69/0.97  --inst_sos_phase                        true
% 1.69/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.97  --inst_lit_sel_side                     num_symb
% 1.69/0.97  --inst_solver_per_active                1400
% 1.69/0.97  --inst_solver_calls_frac                1.
% 1.69/0.97  --inst_passive_queue_type               priority_queues
% 1.69/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.97  --inst_passive_queues_freq              [25;2]
% 1.69/0.97  --inst_dismatching                      true
% 1.69/0.97  --inst_eager_unprocessed_to_passive     true
% 1.69/0.97  --inst_prop_sim_given                   true
% 1.69/0.97  --inst_prop_sim_new                     false
% 1.69/0.97  --inst_subs_new                         false
% 1.69/0.97  --inst_eq_res_simp                      false
% 1.69/0.97  --inst_subs_given                       false
% 1.69/0.97  --inst_orphan_elimination               true
% 1.69/0.97  --inst_learning_loop_flag               true
% 1.69/0.97  --inst_learning_start                   3000
% 1.69/0.97  --inst_learning_factor                  2
% 1.69/0.97  --inst_start_prop_sim_after_learn       3
% 1.69/0.97  --inst_sel_renew                        solver
% 1.69/0.97  --inst_lit_activity_flag                true
% 1.69/0.97  --inst_restr_to_given                   false
% 1.69/0.97  --inst_activity_threshold               500
% 1.69/0.97  --inst_out_proof                        true
% 1.69/0.97  
% 1.69/0.97  ------ Resolution Options
% 1.69/0.97  
% 1.69/0.97  --resolution_flag                       true
% 1.69/0.97  --res_lit_sel                           adaptive
% 1.69/0.97  --res_lit_sel_side                      none
% 1.69/0.97  --res_ordering                          kbo
% 1.69/0.97  --res_to_prop_solver                    active
% 1.69/0.97  --res_prop_simpl_new                    false
% 1.69/0.97  --res_prop_simpl_given                  true
% 1.69/0.97  --res_passive_queue_type                priority_queues
% 1.69/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.97  --res_passive_queues_freq               [15;5]
% 1.69/0.97  --res_forward_subs                      full
% 1.69/0.97  --res_backward_subs                     full
% 1.69/0.97  --res_forward_subs_resolution           true
% 1.69/0.97  --res_backward_subs_resolution          true
% 1.69/0.97  --res_orphan_elimination                true
% 1.69/0.97  --res_time_limit                        2.
% 1.69/0.97  --res_out_proof                         true
% 1.69/0.97  
% 1.69/0.97  ------ Superposition Options
% 1.69/0.97  
% 1.69/0.97  --superposition_flag                    true
% 1.69/0.97  --sup_passive_queue_type                priority_queues
% 1.69/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.97  --demod_completeness_check              fast
% 1.69/0.97  --demod_use_ground                      true
% 1.69/0.97  --sup_to_prop_solver                    passive
% 1.69/0.97  --sup_prop_simpl_new                    true
% 1.69/0.97  --sup_prop_simpl_given                  true
% 1.69/0.97  --sup_fun_splitting                     false
% 1.69/0.97  --sup_smt_interval                      50000
% 1.69/0.97  
% 1.69/0.97  ------ Superposition Simplification Setup
% 1.69/0.97  
% 1.69/0.97  --sup_indices_passive                   []
% 1.69/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_full_bw                           [BwDemod]
% 1.69/0.97  --sup_immed_triv                        [TrivRules]
% 1.69/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_immed_bw_main                     []
% 1.69/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.97  
% 1.69/0.97  ------ Combination Options
% 1.69/0.97  
% 1.69/0.97  --comb_res_mult                         3
% 1.69/0.97  --comb_sup_mult                         2
% 1.69/0.97  --comb_inst_mult                        10
% 1.69/0.97  
% 1.69/0.97  ------ Debug Options
% 1.69/0.97  
% 1.69/0.97  --dbg_backtrace                         false
% 1.69/0.97  --dbg_dump_prop_clauses                 false
% 1.69/0.97  --dbg_dump_prop_clauses_file            -
% 1.69/0.97  --dbg_out_stat                          false
% 1.69/0.97  ------ Parsing...
% 1.69/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.69/0.97  ------ Proving...
% 1.69/0.97  ------ Problem Properties 
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  clauses                                 14
% 1.69/0.97  conjectures                             3
% 1.69/0.97  EPR                                     4
% 1.69/0.97  Horn                                    12
% 1.69/0.97  unary                                   4
% 1.69/0.97  binary                                  5
% 1.69/0.97  lits                                    30
% 1.69/0.97  lits eq                                 18
% 1.69/0.97  fd_pure                                 0
% 1.69/0.97  fd_pseudo                               0
% 1.69/0.97  fd_cond                                 0
% 1.69/0.97  fd_pseudo_cond                          0
% 1.69/0.97  AC symbols                              0
% 1.69/0.97  
% 1.69/0.97  ------ Schedule dynamic 5 is on 
% 1.69/0.97  
% 1.69/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  ------ 
% 1.69/0.97  Current options:
% 1.69/0.97  ------ 
% 1.69/0.97  
% 1.69/0.97  ------ Input Options
% 1.69/0.97  
% 1.69/0.97  --out_options                           all
% 1.69/0.97  --tptp_safe_out                         true
% 1.69/0.97  --problem_path                          ""
% 1.69/0.97  --include_path                          ""
% 1.69/0.97  --clausifier                            res/vclausify_rel
% 1.69/0.97  --clausifier_options                    --mode clausify
% 1.69/0.97  --stdin                                 false
% 1.69/0.97  --stats_out                             all
% 1.69/0.97  
% 1.69/0.97  ------ General Options
% 1.69/0.97  
% 1.69/0.97  --fof                                   false
% 1.69/0.97  --time_out_real                         305.
% 1.69/0.97  --time_out_virtual                      -1.
% 1.69/0.97  --symbol_type_check                     false
% 1.69/0.97  --clausify_out                          false
% 1.69/0.97  --sig_cnt_out                           false
% 1.69/0.97  --trig_cnt_out                          false
% 1.69/0.97  --trig_cnt_out_tolerance                1.
% 1.69/0.97  --trig_cnt_out_sk_spl                   false
% 1.69/0.97  --abstr_cl_out                          false
% 1.69/0.97  
% 1.69/0.97  ------ Global Options
% 1.69/0.97  
% 1.69/0.97  --schedule                              default
% 1.69/0.97  --add_important_lit                     false
% 1.69/0.97  --prop_solver_per_cl                    1000
% 1.69/0.97  --min_unsat_core                        false
% 1.69/0.97  --soft_assumptions                      false
% 1.69/0.97  --soft_lemma_size                       3
% 1.69/0.97  --prop_impl_unit_size                   0
% 1.69/0.97  --prop_impl_unit                        []
% 1.69/0.97  --share_sel_clauses                     true
% 1.69/0.97  --reset_solvers                         false
% 1.69/0.97  --bc_imp_inh                            [conj_cone]
% 1.69/0.97  --conj_cone_tolerance                   3.
% 1.69/0.97  --extra_neg_conj                        none
% 1.69/0.97  --large_theory_mode                     true
% 1.69/0.97  --prolific_symb_bound                   200
% 1.69/0.97  --lt_threshold                          2000
% 1.69/0.97  --clause_weak_htbl                      true
% 1.69/0.97  --gc_record_bc_elim                     false
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing Options
% 1.69/0.97  
% 1.69/0.97  --preprocessing_flag                    true
% 1.69/0.97  --time_out_prep_mult                    0.1
% 1.69/0.97  --splitting_mode                        input
% 1.69/0.97  --splitting_grd                         true
% 1.69/0.97  --splitting_cvd                         false
% 1.69/0.97  --splitting_cvd_svl                     false
% 1.69/0.97  --splitting_nvd                         32
% 1.69/0.97  --sub_typing                            true
% 1.69/0.97  --prep_gs_sim                           true
% 1.69/0.97  --prep_unflatten                        true
% 1.69/0.97  --prep_res_sim                          true
% 1.69/0.97  --prep_upred                            true
% 1.69/0.97  --prep_sem_filter                       exhaustive
% 1.69/0.97  --prep_sem_filter_out                   false
% 1.69/0.97  --pred_elim                             true
% 1.69/0.97  --res_sim_input                         true
% 1.69/0.97  --eq_ax_congr_red                       true
% 1.69/0.97  --pure_diseq_elim                       true
% 1.69/0.97  --brand_transform                       false
% 1.69/0.97  --non_eq_to_eq                          false
% 1.69/0.97  --prep_def_merge                        true
% 1.69/0.97  --prep_def_merge_prop_impl              false
% 1.69/0.97  --prep_def_merge_mbd                    true
% 1.69/0.97  --prep_def_merge_tr_red                 false
% 1.69/0.97  --prep_def_merge_tr_cl                  false
% 1.69/0.97  --smt_preprocessing                     true
% 1.69/0.97  --smt_ac_axioms                         fast
% 1.69/0.97  --preprocessed_out                      false
% 1.69/0.97  --preprocessed_stats                    false
% 1.69/0.97  
% 1.69/0.97  ------ Abstraction refinement Options
% 1.69/0.97  
% 1.69/0.97  --abstr_ref                             []
% 1.69/0.97  --abstr_ref_prep                        false
% 1.69/0.97  --abstr_ref_until_sat                   false
% 1.69/0.97  --abstr_ref_sig_restrict                funpre
% 1.69/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.97  --abstr_ref_under                       []
% 1.69/0.97  
% 1.69/0.97  ------ SAT Options
% 1.69/0.97  
% 1.69/0.97  --sat_mode                              false
% 1.69/0.97  --sat_fm_restart_options                ""
% 1.69/0.97  --sat_gr_def                            false
% 1.69/0.97  --sat_epr_types                         true
% 1.69/0.97  --sat_non_cyclic_types                  false
% 1.69/0.97  --sat_finite_models                     false
% 1.69/0.97  --sat_fm_lemmas                         false
% 1.69/0.97  --sat_fm_prep                           false
% 1.69/0.97  --sat_fm_uc_incr                        true
% 1.69/0.97  --sat_out_model                         small
% 1.69/0.97  --sat_out_clauses                       false
% 1.69/0.97  
% 1.69/0.97  ------ QBF Options
% 1.69/0.97  
% 1.69/0.97  --qbf_mode                              false
% 1.69/0.97  --qbf_elim_univ                         false
% 1.69/0.97  --qbf_dom_inst                          none
% 1.69/0.97  --qbf_dom_pre_inst                      false
% 1.69/0.97  --qbf_sk_in                             false
% 1.69/0.97  --qbf_pred_elim                         true
% 1.69/0.97  --qbf_split                             512
% 1.69/0.97  
% 1.69/0.97  ------ BMC1 Options
% 1.69/0.97  
% 1.69/0.97  --bmc1_incremental                      false
% 1.69/0.97  --bmc1_axioms                           reachable_all
% 1.69/0.97  --bmc1_min_bound                        0
% 1.69/0.97  --bmc1_max_bound                        -1
% 1.69/0.97  --bmc1_max_bound_default                -1
% 1.69/0.97  --bmc1_symbol_reachability              true
% 1.69/0.97  --bmc1_property_lemmas                  false
% 1.69/0.97  --bmc1_k_induction                      false
% 1.69/0.97  --bmc1_non_equiv_states                 false
% 1.69/0.97  --bmc1_deadlock                         false
% 1.69/0.97  --bmc1_ucm                              false
% 1.69/0.97  --bmc1_add_unsat_core                   none
% 1.69/0.97  --bmc1_unsat_core_children              false
% 1.69/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.97  --bmc1_out_stat                         full
% 1.69/0.97  --bmc1_ground_init                      false
% 1.69/0.97  --bmc1_pre_inst_next_state              false
% 1.69/0.97  --bmc1_pre_inst_state                   false
% 1.69/0.97  --bmc1_pre_inst_reach_state             false
% 1.69/0.97  --bmc1_out_unsat_core                   false
% 1.69/0.97  --bmc1_aig_witness_out                  false
% 1.69/0.97  --bmc1_verbose                          false
% 1.69/0.97  --bmc1_dump_clauses_tptp                false
% 1.69/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.97  --bmc1_dump_file                        -
% 1.69/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.97  --bmc1_ucm_extend_mode                  1
% 1.69/0.97  --bmc1_ucm_init_mode                    2
% 1.69/0.97  --bmc1_ucm_cone_mode                    none
% 1.69/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.97  --bmc1_ucm_relax_model                  4
% 1.69/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.97  --bmc1_ucm_layered_model                none
% 1.69/0.97  --bmc1_ucm_max_lemma_size               10
% 1.69/0.97  
% 1.69/0.97  ------ AIG Options
% 1.69/0.97  
% 1.69/0.97  --aig_mode                              false
% 1.69/0.97  
% 1.69/0.97  ------ Instantiation Options
% 1.69/0.97  
% 1.69/0.97  --instantiation_flag                    true
% 1.69/0.97  --inst_sos_flag                         false
% 1.69/0.97  --inst_sos_phase                        true
% 1.69/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.97  --inst_lit_sel_side                     none
% 1.69/0.97  --inst_solver_per_active                1400
% 1.69/0.97  --inst_solver_calls_frac                1.
% 1.69/0.97  --inst_passive_queue_type               priority_queues
% 1.69/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.97  --inst_passive_queues_freq              [25;2]
% 1.69/0.97  --inst_dismatching                      true
% 1.69/0.97  --inst_eager_unprocessed_to_passive     true
% 1.69/0.97  --inst_prop_sim_given                   true
% 1.69/0.97  --inst_prop_sim_new                     false
% 1.69/0.97  --inst_subs_new                         false
% 1.69/0.97  --inst_eq_res_simp                      false
% 1.69/0.97  --inst_subs_given                       false
% 1.69/0.97  --inst_orphan_elimination               true
% 1.69/0.97  --inst_learning_loop_flag               true
% 1.69/0.97  --inst_learning_start                   3000
% 1.69/0.97  --inst_learning_factor                  2
% 1.69/0.97  --inst_start_prop_sim_after_learn       3
% 1.69/0.97  --inst_sel_renew                        solver
% 1.69/0.97  --inst_lit_activity_flag                true
% 1.69/0.97  --inst_restr_to_given                   false
% 1.69/0.97  --inst_activity_threshold               500
% 1.69/0.97  --inst_out_proof                        true
% 1.69/0.97  
% 1.69/0.97  ------ Resolution Options
% 1.69/0.97  
% 1.69/0.97  --resolution_flag                       false
% 1.69/0.97  --res_lit_sel                           adaptive
% 1.69/0.97  --res_lit_sel_side                      none
% 1.69/0.97  --res_ordering                          kbo
% 1.69/0.97  --res_to_prop_solver                    active
% 1.69/0.97  --res_prop_simpl_new                    false
% 1.69/0.97  --res_prop_simpl_given                  true
% 1.69/0.97  --res_passive_queue_type                priority_queues
% 1.69/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.97  --res_passive_queues_freq               [15;5]
% 1.69/0.97  --res_forward_subs                      full
% 1.69/0.97  --res_backward_subs                     full
% 1.69/0.97  --res_forward_subs_resolution           true
% 1.69/0.97  --res_backward_subs_resolution          true
% 1.69/0.97  --res_orphan_elimination                true
% 1.69/0.97  --res_time_limit                        2.
% 1.69/0.97  --res_out_proof                         true
% 1.69/0.97  
% 1.69/0.97  ------ Superposition Options
% 1.69/0.97  
% 1.69/0.97  --superposition_flag                    true
% 1.69/0.97  --sup_passive_queue_type                priority_queues
% 1.69/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.97  --demod_completeness_check              fast
% 1.69/0.97  --demod_use_ground                      true
% 1.69/0.97  --sup_to_prop_solver                    passive
% 1.69/0.97  --sup_prop_simpl_new                    true
% 1.69/0.97  --sup_prop_simpl_given                  true
% 1.69/0.97  --sup_fun_splitting                     false
% 1.69/0.97  --sup_smt_interval                      50000
% 1.69/0.97  
% 1.69/0.97  ------ Superposition Simplification Setup
% 1.69/0.97  
% 1.69/0.97  --sup_indices_passive                   []
% 1.69/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_full_bw                           [BwDemod]
% 1.69/0.97  --sup_immed_triv                        [TrivRules]
% 1.69/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_immed_bw_main                     []
% 1.69/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.97  
% 1.69/0.97  ------ Combination Options
% 1.69/0.97  
% 1.69/0.97  --comb_res_mult                         3
% 1.69/0.97  --comb_sup_mult                         2
% 1.69/0.97  --comb_inst_mult                        10
% 1.69/0.97  
% 1.69/0.97  ------ Debug Options
% 1.69/0.97  
% 1.69/0.97  --dbg_backtrace                         false
% 1.69/0.97  --dbg_dump_prop_clauses                 false
% 1.69/0.97  --dbg_dump_prop_clauses_file            -
% 1.69/0.97  --dbg_out_stat                          false
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  ------ Proving...
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  % SZS status Theorem for theBenchmark.p
% 1.69/0.97  
% 1.69/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.69/0.97  
% 1.69/0.97  fof(f10,conjecture,(
% 1.69/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f11,negated_conjecture,(
% 1.69/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.97    inference(negated_conjecture,[],[f10])).
% 1.69/0.97  
% 1.69/0.97  fof(f12,plain,(
% 1.69/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.97    inference(pure_predicate_removal,[],[f11])).
% 1.69/0.97  
% 1.69/0.97  fof(f23,plain,(
% 1.69/0.97    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)))),
% 1.69/0.97    inference(ennf_transformation,[],[f12])).
% 1.69/0.97  
% 1.69/0.97  fof(f24,plain,(
% 1.69/0.97    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1))),
% 1.69/0.97    inference(flattening,[],[f23])).
% 1.69/0.97  
% 1.69/0.97  fof(f26,plain,(
% 1.69/0.97    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1))),
% 1.69/0.97    introduced(choice_axiom,[])).
% 1.69/0.97  
% 1.69/0.97  fof(f27,plain,(
% 1.69/0.97    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1)),
% 1.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).
% 1.69/0.97  
% 1.69/0.97  fof(f42,plain,(
% 1.69/0.97    v1_funct_2(sK3,sK0,sK1)),
% 1.69/0.97    inference(cnf_transformation,[],[f27])).
% 1.69/0.97  
% 1.69/0.97  fof(f9,axiom,(
% 1.69/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f21,plain,(
% 1.69/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(ennf_transformation,[],[f9])).
% 1.69/0.97  
% 1.69/0.97  fof(f22,plain,(
% 1.69/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(flattening,[],[f21])).
% 1.69/0.97  
% 1.69/0.97  fof(f25,plain,(
% 1.69/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(nnf_transformation,[],[f22])).
% 1.69/0.97  
% 1.69/0.97  fof(f36,plain,(
% 1.69/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.97    inference(cnf_transformation,[],[f25])).
% 1.69/0.97  
% 1.69/0.97  fof(f43,plain,(
% 1.69/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.97    inference(cnf_transformation,[],[f27])).
% 1.69/0.97  
% 1.69/0.97  fof(f6,axiom,(
% 1.69/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f18,plain,(
% 1.69/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(ennf_transformation,[],[f6])).
% 1.69/0.97  
% 1.69/0.97  fof(f33,plain,(
% 1.69/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.97    inference(cnf_transformation,[],[f18])).
% 1.69/0.97  
% 1.69/0.97  fof(f5,axiom,(
% 1.69/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f16,plain,(
% 1.69/0.97    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.69/0.97    inference(ennf_transformation,[],[f5])).
% 1.69/0.97  
% 1.69/0.97  fof(f17,plain,(
% 1.69/0.97    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.69/0.97    inference(flattening,[],[f16])).
% 1.69/0.97  
% 1.69/0.97  fof(f32,plain,(
% 1.69/0.97    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.69/0.97    inference(cnf_transformation,[],[f17])).
% 1.69/0.97  
% 1.69/0.97  fof(f7,axiom,(
% 1.69/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f19,plain,(
% 1.69/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(ennf_transformation,[],[f7])).
% 1.69/0.97  
% 1.69/0.97  fof(f34,plain,(
% 1.69/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.97    inference(cnf_transformation,[],[f19])).
% 1.69/0.97  
% 1.69/0.97  fof(f46,plain,(
% 1.69/0.97    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.69/0.97    inference(cnf_transformation,[],[f27])).
% 1.69/0.97  
% 1.69/0.97  fof(f8,axiom,(
% 1.69/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f20,plain,(
% 1.69/0.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.97    inference(ennf_transformation,[],[f8])).
% 1.69/0.97  
% 1.69/0.97  fof(f35,plain,(
% 1.69/0.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.97    inference(cnf_transformation,[],[f20])).
% 1.69/0.97  
% 1.69/0.97  fof(f3,axiom,(
% 1.69/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f15,plain,(
% 1.69/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.97    inference(ennf_transformation,[],[f3])).
% 1.69/0.97  
% 1.69/0.97  fof(f30,plain,(
% 1.69/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.69/0.97    inference(cnf_transformation,[],[f15])).
% 1.69/0.97  
% 1.69/0.97  fof(f4,axiom,(
% 1.69/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f31,plain,(
% 1.69/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.69/0.97    inference(cnf_transformation,[],[f4])).
% 1.69/0.97  
% 1.69/0.97  fof(f2,axiom,(
% 1.69/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f29,plain,(
% 1.69/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.69/0.97    inference(cnf_transformation,[],[f2])).
% 1.69/0.97  
% 1.69/0.97  fof(f1,axiom,(
% 1.69/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.97  
% 1.69/0.97  fof(f13,plain,(
% 1.69/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.69/0.97    inference(ennf_transformation,[],[f1])).
% 1.69/0.97  
% 1.69/0.97  fof(f14,plain,(
% 1.69/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.69/0.97    inference(flattening,[],[f13])).
% 1.69/0.97  
% 1.69/0.97  fof(f28,plain,(
% 1.69/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.69/0.97    inference(cnf_transformation,[],[f14])).
% 1.69/0.97  
% 1.69/0.97  fof(f45,plain,(
% 1.69/0.97    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.69/0.97    inference(cnf_transformation,[],[f27])).
% 1.69/0.97  
% 1.69/0.97  fof(f44,plain,(
% 1.69/0.97    r1_tarski(sK2,sK0)),
% 1.69/0.97    inference(cnf_transformation,[],[f27])).
% 1.69/0.97  
% 1.69/0.97  cnf(c_18,negated_conjecture,
% 1.69/0.97      ( v1_funct_2(sK3,sK0,sK1) ),
% 1.69/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_13,plain,
% 1.69/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.97      | k1_relset_1(X1,X2,X0) = X1
% 1.69/0.97      | k1_xboole_0 = X2 ),
% 1.69/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_17,negated_conjecture,
% 1.69/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.69/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_218,plain,
% 1.69/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.69/0.97      | k1_relset_1(X1,X2,X0) = X1
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | sK3 != X0
% 1.69/0.97      | k1_xboole_0 = X2 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_219,plain,
% 1.69/0.97      ( ~ v1_funct_2(sK3,X0,X1)
% 1.69/0.97      | k1_relset_1(X0,X1,sK3) = X0
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | k1_xboole_0 = X1 ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_218]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_392,plain,
% 1.69/0.97      ( k1_relset_1(X0,X1,sK3) = X0
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | sK3 != sK3
% 1.69/0.97      | sK1 != X1
% 1.69/0.97      | sK0 != X0
% 1.69/0.97      | k1_xboole_0 = X1 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_219]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_393,plain,
% 1.69/0.97      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | k1_xboole_0 = sK1 ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_392]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_453,plain,
% 1.69/0.97      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 1.69/0.97      inference(equality_resolution_simp,[status(thm)],[c_393]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_502,plain,
% 1.69/0.97      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_453]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_5,plain,
% 1.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.69/0.97      inference(cnf_transformation,[],[f33]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_272,plain,
% 1.69/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | sK3 != X2 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_273,plain,
% 1.69/0.97      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_272]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_505,plain,
% 1.69/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | k1_relset_1(X0_45,X1_45,sK3) = k1_relat_1(sK3) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_273]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_791,plain,
% 1.69/0.97      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 1.69/0.97      inference(equality_resolution,[status(thm)],[c_505]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1060,plain,
% 1.69/0.97      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 1.69/0.97      inference(superposition,[status(thm)],[c_502,c_791]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_4,plain,
% 1.69/0.97      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 1.69/0.97      | ~ r1_tarski(X0,k1_relat_1(X1))
% 1.69/0.97      | ~ v1_relat_1(X1) ),
% 1.69/0.97      inference(cnf_transformation,[],[f32]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_512,plain,
% 1.69/0.97      ( r1_tarski(X0_45,k10_relat_1(X1_45,k9_relat_1(X1_45,X0_45)))
% 1.69/0.97      | ~ r1_tarski(X0_45,k1_relat_1(X1_45))
% 1.69/0.97      | ~ v1_relat_1(X1_45) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_679,plain,
% 1.69/0.97      ( r1_tarski(X0_45,k10_relat_1(X1_45,k9_relat_1(X1_45,X0_45))) = iProver_top
% 1.69/0.97      | r1_tarski(X0_45,k1_relat_1(X1_45)) != iProver_top
% 1.69/0.97      | v1_relat_1(X1_45) != iProver_top ),
% 1.69/0.97      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_6,plain,
% 1.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.69/0.97      inference(cnf_transformation,[],[f34]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_263,plain,
% 1.69/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | sK3 != X2 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_264,plain,
% 1.69/0.97      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_263]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_506,plain,
% 1.69/0.97      ( k7_relset_1(X0_45,X1_45,sK3,X2_45) = k9_relat_1(sK3,X2_45)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_264]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_806,plain,
% 1.69/0.97      ( k7_relset_1(sK0,sK1,sK3,X0_45) = k9_relat_1(sK3,X0_45) ),
% 1.69/0.97      inference(equality_resolution,[status(thm)],[c_506]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_14,negated_conjecture,
% 1.69/0.97      ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 1.69/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_511,negated_conjecture,
% 1.69/0.97      ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_680,plain,
% 1.69/0.97      ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
% 1.69/0.97      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1161,plain,
% 1.69/0.97      ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
% 1.69/0.97      inference(demodulation,[status(thm)],[c_806,c_680]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_7,plain,
% 1.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.69/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_254,plain,
% 1.69/0.97      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | sK3 != X2 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_255,plain,
% 1.69/0.97      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_254]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_507,plain,
% 1.69/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | k8_relset_1(X0_45,X1_45,sK3,X0_47) = k10_relat_1(sK3,X0_47) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_255]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_810,plain,
% 1.69/0.97      ( k8_relset_1(sK0,sK1,sK3,X0_47) = k10_relat_1(sK3,X0_47) ),
% 1.69/0.97      inference(equality_resolution,[status(thm)],[c_507]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1223,plain,
% 1.69/0.97      ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
% 1.69/0.97      inference(demodulation,[status(thm)],[c_1161,c_810]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1226,plain,
% 1.69/0.97      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
% 1.69/0.97      | v1_relat_1(sK3) != iProver_top ),
% 1.69/0.97      inference(superposition,[status(thm)],[c_679,c_1223]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_518,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_768,plain,
% 1.69/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_518]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_2,plain,
% 1.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.69/0.97      | ~ v1_relat_1(X1)
% 1.69/0.97      | v1_relat_1(X0) ),
% 1.69/0.97      inference(cnf_transformation,[],[f30]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_203,plain,
% 1.69/0.97      ( ~ v1_relat_1(X0)
% 1.69/0.97      | v1_relat_1(X1)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 1.69/0.97      | sK3 != X1 ),
% 1.69/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_204,plain,
% 1.69/0.97      ( ~ v1_relat_1(X0)
% 1.69/0.97      | v1_relat_1(sK3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 1.69/0.97      inference(unflattening,[status(thm)],[c_203]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_508,plain,
% 1.69/0.97      ( ~ v1_relat_1(X0_45)
% 1.69/0.97      | v1_relat_1(sK3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_204]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_763,plain,
% 1.69/0.97      ( ~ v1_relat_1(k2_zfmisc_1(X0_45,X1_45))
% 1.69/0.97      | v1_relat_1(sK3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_508]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_842,plain,
% 1.69/0.97      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | v1_relat_1(sK3)
% 1.69/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_763]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_843,plain,
% 1.69/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.69/0.97      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 1.69/0.97      | v1_relat_1(sK3) = iProver_top ),
% 1.69/0.97      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_3,plain,
% 1.69/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.69/0.97      inference(cnf_transformation,[],[f31]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_513,plain,
% 1.69/0.97      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_954,plain,
% 1.69/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_513]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_955,plain,
% 1.69/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 1.69/0.97      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1327,plain,
% 1.69/0.97      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 1.69/0.97      inference(global_propositional_subsumption,
% 1.69/0.97                [status(thm)],
% 1.69/0.97                [c_1226,c_768,c_843,c_955]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1332,plain,
% 1.69/0.97      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK0) != iProver_top ),
% 1.69/0.97      inference(superposition,[status(thm)],[c_1060,c_1327]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1,plain,
% 1.69/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 1.69/0.97      inference(cnf_transformation,[],[f29]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_514,plain,
% 1.69/0.97      ( r1_tarski(k1_xboole_0,X0_45) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1287,plain,
% 1.69/0.97      ( r1_tarski(k1_xboole_0,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_514]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_523,plain,
% 1.69/0.97      ( ~ r1_tarski(X0_45,X1_45)
% 1.69/0.97      | r1_tarski(X2_45,X3_45)
% 1.69/0.97      | X2_45 != X0_45
% 1.69/0.97      | X3_45 != X1_45 ),
% 1.69/0.97      theory(equality) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_818,plain,
% 1.69/0.97      ( ~ r1_tarski(X0_45,X1_45)
% 1.69/0.97      | r1_tarski(sK2,X2_45)
% 1.69/0.97      | X2_45 != X1_45
% 1.69/0.97      | sK2 != X0_45 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_523]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_925,plain,
% 1.69/0.97      ( ~ r1_tarski(sK2,X0_45)
% 1.69/0.97      | r1_tarski(sK2,X1_45)
% 1.69/0.97      | X1_45 != X0_45
% 1.69/0.97      | sK2 != sK2 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_818]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1172,plain,
% 1.69/0.97      ( r1_tarski(sK2,X0_45)
% 1.69/0.97      | ~ r1_tarski(sK2,sK0)
% 1.69/0.97      | X0_45 != sK0
% 1.69/0.97      | sK2 != sK2 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_925]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_1174,plain,
% 1.69/0.97      ( ~ r1_tarski(sK2,sK0)
% 1.69/0.97      | r1_tarski(sK2,k1_xboole_0)
% 1.69/0.97      | sK2 != sK2
% 1.69/0.97      | k1_xboole_0 != sK0 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_1172]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_520,plain,
% 1.69/0.97      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.69/0.97      theory(equality) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_974,plain,
% 1.69/0.97      ( X0_45 != X1_45 | X0_45 = sK1 | sK1 != X1_45 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_520]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_975,plain,
% 1.69/0.97      ( sK1 != k1_xboole_0
% 1.69/0.97      | k1_xboole_0 = sK1
% 1.69/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_974]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_517,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_824,plain,
% 1.69/0.97      ( sK2 = sK2 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_517]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_0,plain,
% 1.69/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.69/0.97      inference(cnf_transformation,[],[f28]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_515,plain,
% 1.69/0.97      ( ~ r1_tarski(X0_45,X1_45)
% 1.69/0.97      | ~ r1_tarski(X2_45,X0_45)
% 1.69/0.97      | r1_tarski(X2_45,X1_45) ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_781,plain,
% 1.69/0.97      ( ~ r1_tarski(X0_45,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
% 1.69/0.97      | ~ r1_tarski(sK2,X0_45)
% 1.69/0.97      | r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_515]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_783,plain,
% 1.69/0.97      ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
% 1.69/0.97      | ~ r1_tarski(sK2,k1_xboole_0)
% 1.69/0.97      | ~ r1_tarski(k1_xboole_0,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_781]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_15,negated_conjecture,
% 1.69/0.97      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.69/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_510,negated_conjecture,
% 1.69/0.97      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.69/0.97      inference(subtyping,[status(esa)],[c_15]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_544,plain,
% 1.69/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 1.69/0.97      inference(instantiation,[status(thm)],[c_517]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_16,negated_conjecture,
% 1.69/0.97      ( r1_tarski(sK2,sK0) ),
% 1.69/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(c_21,plain,
% 1.69/0.97      ( r1_tarski(sK2,sK0) = iProver_top ),
% 1.69/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.69/0.97  
% 1.69/0.97  cnf(contradiction,plain,
% 1.69/0.97      ( $false ),
% 1.69/0.97      inference(minisat,
% 1.69/0.97                [status(thm)],
% 1.69/0.97                [c_1332,c_1287,c_1174,c_975,c_824,c_783,c_510,c_544,c_14,
% 1.69/0.97                 c_21,c_16]) ).
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.69/0.97  
% 1.69/0.97  ------                               Statistics
% 1.69/0.97  
% 1.69/0.97  ------ General
% 1.69/0.97  
% 1.69/0.97  abstr_ref_over_cycles:                  0
% 1.69/0.97  abstr_ref_under_cycles:                 0
% 1.69/0.97  gc_basic_clause_elim:                   0
% 1.69/0.97  forced_gc_time:                         0
% 1.69/0.97  parsing_time:                           0.008
% 1.69/0.97  unif_index_cands_time:                  0.
% 1.69/0.97  unif_index_add_time:                    0.
% 1.69/0.97  orderings_time:                         0.
% 1.69/0.97  out_proof_time:                         0.009
% 1.69/0.97  total_time:                             0.078
% 1.69/0.97  num_of_symbols:                         51
% 1.69/0.97  num_of_terms:                           1489
% 1.69/0.97  
% 1.69/0.97  ------ Preprocessing
% 1.69/0.97  
% 1.69/0.97  num_of_splits:                          0
% 1.69/0.97  num_of_split_atoms:                     0
% 1.69/0.97  num_of_reused_defs:                     0
% 1.69/0.97  num_eq_ax_congr_red:                    8
% 1.69/0.97  num_of_sem_filtered_clauses:            1
% 1.69/0.97  num_of_subtypes:                        3
% 1.69/0.97  monotx_restored_types:                  0
% 1.69/0.97  sat_num_of_epr_types:                   0
% 1.69/0.97  sat_num_of_non_cyclic_types:            0
% 1.69/0.97  sat_guarded_non_collapsed_types:        0
% 1.69/0.97  num_pure_diseq_elim:                    0
% 1.69/0.97  simp_replaced_by:                       0
% 1.69/0.97  res_preprocessed:                       94
% 1.69/0.97  prep_upred:                             0
% 1.69/0.97  prep_unflattend:                        26
% 1.69/0.97  smt_new_axioms:                         0
% 1.69/0.97  pred_elim_cands:                        2
% 1.69/0.97  pred_elim:                              2
% 1.69/0.97  pred_elim_cl:                           5
% 1.69/0.97  pred_elim_cycles:                       4
% 1.69/0.97  merged_defs:                            0
% 1.69/0.97  merged_defs_ncl:                        0
% 1.69/0.97  bin_hyper_res:                          0
% 1.69/0.97  prep_cycles:                            4
% 1.69/0.97  pred_elim_time:                         0.006
% 1.69/0.97  splitting_time:                         0.
% 1.69/0.97  sem_filter_time:                        0.
% 1.69/0.97  monotx_time:                            0.
% 1.69/0.97  subtype_inf_time:                       0.001
% 1.69/0.97  
% 1.69/0.97  ------ Problem properties
% 1.69/0.97  
% 1.69/0.97  clauses:                                14
% 1.69/0.97  conjectures:                            3
% 1.69/0.97  epr:                                    4
% 1.69/0.97  horn:                                   12
% 1.69/0.97  ground:                                 6
% 1.69/0.97  unary:                                  4
% 1.69/0.97  binary:                                 5
% 1.69/0.97  lits:                                   30
% 1.69/0.97  lits_eq:                                18
% 1.69/0.97  fd_pure:                                0
% 1.69/0.97  fd_pseudo:                              0
% 1.69/0.97  fd_cond:                                0
% 1.69/0.97  fd_pseudo_cond:                         0
% 1.69/0.97  ac_symbols:                             0
% 1.69/0.97  
% 1.69/0.97  ------ Propositional Solver
% 1.69/0.97  
% 1.69/0.97  prop_solver_calls:                      27
% 1.69/0.97  prop_fast_solver_calls:                 534
% 1.69/0.97  smt_solver_calls:                       0
% 1.69/0.97  smt_fast_solver_calls:                  0
% 1.69/0.97  prop_num_of_clauses:                    429
% 1.69/0.97  prop_preprocess_simplified:             2274
% 1.69/0.97  prop_fo_subsumed:                       3
% 1.69/0.97  prop_solver_time:                       0.
% 1.69/0.97  smt_solver_time:                        0.
% 1.69/0.97  smt_fast_solver_time:                   0.
% 1.69/0.97  prop_fast_solver_time:                  0.
% 1.69/0.97  prop_unsat_core_time:                   0.
% 1.69/0.97  
% 1.69/0.97  ------ QBF
% 1.69/0.97  
% 1.69/0.97  qbf_q_res:                              0
% 1.69/0.97  qbf_num_tautologies:                    0
% 1.69/0.97  qbf_prep_cycles:                        0
% 1.69/0.97  
% 1.69/0.97  ------ BMC1
% 1.69/0.97  
% 1.69/0.97  bmc1_current_bound:                     -1
% 1.69/0.97  bmc1_last_solved_bound:                 -1
% 1.69/0.97  bmc1_unsat_core_size:                   -1
% 1.69/0.97  bmc1_unsat_core_parents_size:           -1
% 1.69/0.97  bmc1_merge_next_fun:                    0
% 1.69/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.69/0.97  
% 1.69/0.97  ------ Instantiation
% 1.69/0.97  
% 1.69/0.97  inst_num_of_clauses:                    135
% 1.69/0.97  inst_num_in_passive:                    48
% 1.69/0.97  inst_num_in_active:                     85
% 1.69/0.97  inst_num_in_unprocessed:                2
% 1.69/0.97  inst_num_of_loops:                      110
% 1.69/0.97  inst_num_of_learning_restarts:          0
% 1.69/0.97  inst_num_moves_active_passive:          22
% 1.69/0.97  inst_lit_activity:                      0
% 1.69/0.97  inst_lit_activity_moves:                0
% 1.69/0.97  inst_num_tautologies:                   0
% 1.69/0.97  inst_num_prop_implied:                  0
% 1.69/0.97  inst_num_existing_simplified:           0
% 1.69/0.97  inst_num_eq_res_simplified:             0
% 1.69/0.97  inst_num_child_elim:                    0
% 1.69/0.97  inst_num_of_dismatching_blockings:      22
% 1.69/0.97  inst_num_of_non_proper_insts:           130
% 1.69/0.97  inst_num_of_duplicates:                 0
% 1.69/0.97  inst_inst_num_from_inst_to_res:         0
% 1.69/0.97  inst_dismatching_checking_time:         0.
% 1.69/0.97  
% 1.69/0.97  ------ Resolution
% 1.69/0.97  
% 1.69/0.97  res_num_of_clauses:                     0
% 1.69/0.97  res_num_in_passive:                     0
% 1.69/0.97  res_num_in_active:                      0
% 1.69/0.97  res_num_of_loops:                       98
% 1.69/0.97  res_forward_subset_subsumed:            16
% 1.69/0.97  res_backward_subset_subsumed:           0
% 1.69/0.97  res_forward_subsumed:                   0
% 1.69/0.97  res_backward_subsumed:                  0
% 1.69/0.97  res_forward_subsumption_resolution:     0
% 1.69/0.97  res_backward_subsumption_resolution:    0
% 1.69/0.97  res_clause_to_clause_subsumption:       30
% 1.69/0.97  res_orphan_elimination:                 0
% 1.69/0.97  res_tautology_del:                      22
% 1.69/0.97  res_num_eq_res_simplified:              1
% 1.69/0.97  res_num_sel_changes:                    0
% 1.69/0.97  res_moves_from_active_to_pass:          0
% 1.69/0.97  
% 1.69/0.97  ------ Superposition
% 1.69/0.97  
% 1.69/0.97  sup_time_total:                         0.
% 1.69/0.97  sup_time_generating:                    0.
% 1.69/0.97  sup_time_sim_full:                      0.
% 1.69/0.97  sup_time_sim_immed:                     0.
% 1.69/0.97  
% 1.69/0.97  sup_num_of_clauses:                     23
% 1.69/0.97  sup_num_in_active:                      20
% 1.69/0.97  sup_num_in_passive:                     3
% 1.69/0.97  sup_num_of_loops:                       20
% 1.69/0.97  sup_fw_superposition:                   6
% 1.69/0.97  sup_bw_superposition:                   2
% 1.69/0.97  sup_immediate_simplified:               1
% 1.69/0.97  sup_given_eliminated:                   0
% 1.69/0.97  comparisons_done:                       0
% 1.69/0.97  comparisons_avoided:                    3
% 1.69/0.97  
% 1.69/0.97  ------ Simplifications
% 1.69/0.97  
% 1.69/0.97  
% 1.69/0.97  sim_fw_subset_subsumed:                 0
% 1.69/0.97  sim_bw_subset_subsumed:                 0
% 1.69/0.97  sim_fw_subsumed:                        1
% 1.69/0.97  sim_bw_subsumed:                        0
% 1.69/0.97  sim_fw_subsumption_res:                 0
% 1.69/0.97  sim_bw_subsumption_res:                 0
% 1.69/0.97  sim_tautology_del:                      0
% 1.69/0.97  sim_eq_tautology_del:                   0
% 1.69/0.97  sim_eq_res_simp:                        0
% 1.69/0.97  sim_fw_demodulated:                     1
% 1.69/0.97  sim_bw_demodulated:                     1
% 1.69/0.97  sim_light_normalised:                   0
% 1.69/0.97  sim_joinable_taut:                      0
% 1.69/0.97  sim_joinable_simp:                      0
% 1.69/0.97  sim_ac_normalised:                      0
% 1.69/0.97  sim_smt_subsumption:                    0
% 1.69/0.97  
%------------------------------------------------------------------------------
