%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:45 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 524 expanded)
%              Number of clauses        :  109 ( 193 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  485 (3299 expanded)
%              Number of equality atoms :  225 (1125 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_621,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1047,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | m1_subset_1(k2_relset_1(X1_53,X2_53,X0_53),k1_zfmisc_1(X2_53)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1036,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_53,X2_53,X0_53),k1_zfmisc_1(X2_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_309,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_313,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_26])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(sK4)
    | X2 != X0
    | k10_relat_1(sK4,k9_relat_1(sK4,X2)) = X2
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_313])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_1049,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_702,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1356,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1357,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_637,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1465,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1466,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_5338,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_35,c_702,c_1357,c_1466])).

cnf(c_5339,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5338])).

cnf(c_623,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1045,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1038,plain,
    ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1376,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1045,c_1038])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_429,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_24,c_21])).

cnf(c_614,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1381,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1376,c_614])).

cnf(c_5344,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5339,c_1381])).

cnf(c_5350,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relset_1(X0_53,sK1,X1_53))) = k2_relset_1(X0_53,sK1,X1_53)
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_5344])).

cnf(c_7755,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relset_1(sK0,sK1,sK3))) = k2_relset_1(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1047,c_5350])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1039,plain,
    ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1387,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1047,c_1039])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X2_53) = k1_relset_1(X1_53,X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1042,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X1_53) = k1_relset_1(X0_53,X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2240,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1045,c_1042])).

cnf(c_2251,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2240,c_614])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1041,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_2221,plain,
    ( k8_relset_1(sK1,sK2,sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_1045,c_1041])).

cnf(c_2699,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_2251,c_2221])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
    | k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1040,plain,
    ( k4_relset_1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_4066,plain,
    ( k4_relset_1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1040])).

cnf(c_4750,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1047,c_4066])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
    | m1_subset_1(k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1037,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53))) != iProver_top
    | m1_subset_1(k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_4796,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4750,c_1037])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6078,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4796,c_32,c_35])).

cnf(c_6094,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_6078,c_1039])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1044,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_4456,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1044])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5278,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4456,c_33])).

cnf(c_5279,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5278])).

cnf(c_5288,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_5279])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5436,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5288,c_30])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_624,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_5440,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5436,c_624])).

cnf(c_6099,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6094,c_5440])).

cnf(c_1033,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1508,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1033])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1360,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_1468,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1469,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_1847,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_32,c_1360,c_1469])).

cnf(c_1507,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1033])).

cnf(c_1841,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1507,c_35,c_1357,c_1466])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_636,plain,
    ( ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k9_relat_1(X1_53,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1035,plain,
    ( k9_relat_1(X0_53,k2_relat_1(X1_53)) = k2_relat_1(k5_relat_1(X1_53,X0_53))
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_2522,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,sK4))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_1035])).

cnf(c_4515,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1847,c_2522])).

cnf(c_6151,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6099,c_4515])).

cnf(c_7775,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7755,c_1387,c_2699,c_6151])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_626,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1618,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1387,c_626])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7775,c_1618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.02  
% 3.79/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.02  
% 3.79/1.02  ------  iProver source info
% 3.79/1.02  
% 3.79/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.02  git: non_committed_changes: false
% 3.79/1.02  git: last_make_outside_of_git: false
% 3.79/1.02  
% 3.79/1.02  ------ 
% 3.79/1.02  
% 3.79/1.02  ------ Input Options
% 3.79/1.02  
% 3.79/1.02  --out_options                           all
% 3.79/1.02  --tptp_safe_out                         true
% 3.79/1.02  --problem_path                          ""
% 3.79/1.02  --include_path                          ""
% 3.79/1.02  --clausifier                            res/vclausify_rel
% 3.79/1.02  --clausifier_options                    --mode clausify
% 3.79/1.02  --stdin                                 false
% 3.79/1.02  --stats_out                             all
% 3.79/1.02  
% 3.79/1.02  ------ General Options
% 3.79/1.02  
% 3.79/1.02  --fof                                   false
% 3.79/1.02  --time_out_real                         305.
% 3.79/1.02  --time_out_virtual                      -1.
% 3.79/1.02  --symbol_type_check                     false
% 3.79/1.02  --clausify_out                          false
% 3.79/1.02  --sig_cnt_out                           false
% 3.79/1.02  --trig_cnt_out                          false
% 3.79/1.02  --trig_cnt_out_tolerance                1.
% 3.79/1.02  --trig_cnt_out_sk_spl                   false
% 3.79/1.02  --abstr_cl_out                          false
% 3.79/1.02  
% 3.79/1.02  ------ Global Options
% 3.79/1.02  
% 3.79/1.02  --schedule                              default
% 3.79/1.02  --add_important_lit                     false
% 3.79/1.02  --prop_solver_per_cl                    1000
% 3.79/1.02  --min_unsat_core                        false
% 3.79/1.02  --soft_assumptions                      false
% 3.79/1.02  --soft_lemma_size                       3
% 3.79/1.02  --prop_impl_unit_size                   0
% 3.79/1.02  --prop_impl_unit                        []
% 3.79/1.02  --share_sel_clauses                     true
% 3.79/1.02  --reset_solvers                         false
% 3.79/1.02  --bc_imp_inh                            [conj_cone]
% 3.79/1.02  --conj_cone_tolerance                   3.
% 3.79/1.02  --extra_neg_conj                        none
% 3.79/1.02  --large_theory_mode                     true
% 3.79/1.02  --prolific_symb_bound                   200
% 3.79/1.02  --lt_threshold                          2000
% 3.79/1.02  --clause_weak_htbl                      true
% 3.79/1.02  --gc_record_bc_elim                     false
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing Options
% 3.79/1.02  
% 3.79/1.02  --preprocessing_flag                    true
% 3.79/1.02  --time_out_prep_mult                    0.1
% 3.79/1.02  --splitting_mode                        input
% 3.79/1.02  --splitting_grd                         true
% 3.79/1.02  --splitting_cvd                         false
% 3.79/1.02  --splitting_cvd_svl                     false
% 3.79/1.02  --splitting_nvd                         32
% 3.79/1.02  --sub_typing                            true
% 3.79/1.02  --prep_gs_sim                           true
% 3.79/1.02  --prep_unflatten                        true
% 3.79/1.02  --prep_res_sim                          true
% 3.79/1.02  --prep_upred                            true
% 3.79/1.02  --prep_sem_filter                       exhaustive
% 3.79/1.02  --prep_sem_filter_out                   false
% 3.79/1.02  --pred_elim                             true
% 3.79/1.02  --res_sim_input                         true
% 3.79/1.02  --eq_ax_congr_red                       true
% 3.79/1.02  --pure_diseq_elim                       true
% 3.79/1.02  --brand_transform                       false
% 3.79/1.02  --non_eq_to_eq                          false
% 3.79/1.02  --prep_def_merge                        true
% 3.79/1.02  --prep_def_merge_prop_impl              false
% 3.79/1.02  --prep_def_merge_mbd                    true
% 3.79/1.02  --prep_def_merge_tr_red                 false
% 3.79/1.02  --prep_def_merge_tr_cl                  false
% 3.79/1.02  --smt_preprocessing                     true
% 3.79/1.02  --smt_ac_axioms                         fast
% 3.79/1.02  --preprocessed_out                      false
% 3.79/1.02  --preprocessed_stats                    false
% 3.79/1.02  
% 3.79/1.02  ------ Abstraction refinement Options
% 3.79/1.02  
% 3.79/1.02  --abstr_ref                             []
% 3.79/1.02  --abstr_ref_prep                        false
% 3.79/1.02  --abstr_ref_until_sat                   false
% 3.79/1.02  --abstr_ref_sig_restrict                funpre
% 3.79/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.02  --abstr_ref_under                       []
% 3.79/1.02  
% 3.79/1.02  ------ SAT Options
% 3.79/1.02  
% 3.79/1.02  --sat_mode                              false
% 3.79/1.02  --sat_fm_restart_options                ""
% 3.79/1.02  --sat_gr_def                            false
% 3.79/1.02  --sat_epr_types                         true
% 3.79/1.02  --sat_non_cyclic_types                  false
% 3.79/1.02  --sat_finite_models                     false
% 3.79/1.02  --sat_fm_lemmas                         false
% 3.79/1.02  --sat_fm_prep                           false
% 3.79/1.02  --sat_fm_uc_incr                        true
% 3.79/1.02  --sat_out_model                         small
% 3.79/1.02  --sat_out_clauses                       false
% 3.79/1.02  
% 3.79/1.02  ------ QBF Options
% 3.79/1.02  
% 3.79/1.02  --qbf_mode                              false
% 3.79/1.02  --qbf_elim_univ                         false
% 3.79/1.02  --qbf_dom_inst                          none
% 3.79/1.02  --qbf_dom_pre_inst                      false
% 3.79/1.02  --qbf_sk_in                             false
% 3.79/1.02  --qbf_pred_elim                         true
% 3.79/1.02  --qbf_split                             512
% 3.79/1.02  
% 3.79/1.02  ------ BMC1 Options
% 3.79/1.02  
% 3.79/1.02  --bmc1_incremental                      false
% 3.79/1.02  --bmc1_axioms                           reachable_all
% 3.79/1.02  --bmc1_min_bound                        0
% 3.79/1.02  --bmc1_max_bound                        -1
% 3.79/1.02  --bmc1_max_bound_default                -1
% 3.79/1.02  --bmc1_symbol_reachability              true
% 3.79/1.02  --bmc1_property_lemmas                  false
% 3.79/1.02  --bmc1_k_induction                      false
% 3.79/1.02  --bmc1_non_equiv_states                 false
% 3.79/1.02  --bmc1_deadlock                         false
% 3.79/1.02  --bmc1_ucm                              false
% 3.79/1.02  --bmc1_add_unsat_core                   none
% 3.79/1.02  --bmc1_unsat_core_children              false
% 3.79/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.02  --bmc1_out_stat                         full
% 3.79/1.02  --bmc1_ground_init                      false
% 3.79/1.02  --bmc1_pre_inst_next_state              false
% 3.79/1.02  --bmc1_pre_inst_state                   false
% 3.79/1.02  --bmc1_pre_inst_reach_state             false
% 3.79/1.02  --bmc1_out_unsat_core                   false
% 3.79/1.02  --bmc1_aig_witness_out                  false
% 3.79/1.02  --bmc1_verbose                          false
% 3.79/1.02  --bmc1_dump_clauses_tptp                false
% 3.79/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.02  --bmc1_dump_file                        -
% 3.79/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.02  --bmc1_ucm_extend_mode                  1
% 3.79/1.02  --bmc1_ucm_init_mode                    2
% 3.79/1.02  --bmc1_ucm_cone_mode                    none
% 3.79/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.02  --bmc1_ucm_relax_model                  4
% 3.79/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.02  --bmc1_ucm_layered_model                none
% 3.79/1.02  --bmc1_ucm_max_lemma_size               10
% 3.79/1.02  
% 3.79/1.02  ------ AIG Options
% 3.79/1.02  
% 3.79/1.02  --aig_mode                              false
% 3.79/1.02  
% 3.79/1.02  ------ Instantiation Options
% 3.79/1.02  
% 3.79/1.02  --instantiation_flag                    true
% 3.79/1.02  --inst_sos_flag                         false
% 3.79/1.02  --inst_sos_phase                        true
% 3.79/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.02  --inst_lit_sel_side                     num_symb
% 3.79/1.02  --inst_solver_per_active                1400
% 3.79/1.02  --inst_solver_calls_frac                1.
% 3.79/1.02  --inst_passive_queue_type               priority_queues
% 3.79/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.02  --inst_passive_queues_freq              [25;2]
% 3.79/1.02  --inst_dismatching                      true
% 3.79/1.02  --inst_eager_unprocessed_to_passive     true
% 3.79/1.02  --inst_prop_sim_given                   true
% 3.79/1.02  --inst_prop_sim_new                     false
% 3.79/1.02  --inst_subs_new                         false
% 3.79/1.02  --inst_eq_res_simp                      false
% 3.79/1.02  --inst_subs_given                       false
% 3.79/1.02  --inst_orphan_elimination               true
% 3.79/1.02  --inst_learning_loop_flag               true
% 3.79/1.02  --inst_learning_start                   3000
% 3.79/1.02  --inst_learning_factor                  2
% 3.79/1.02  --inst_start_prop_sim_after_learn       3
% 3.79/1.02  --inst_sel_renew                        solver
% 3.79/1.02  --inst_lit_activity_flag                true
% 3.79/1.02  --inst_restr_to_given                   false
% 3.79/1.02  --inst_activity_threshold               500
% 3.79/1.02  --inst_out_proof                        true
% 3.79/1.02  
% 3.79/1.02  ------ Resolution Options
% 3.79/1.02  
% 3.79/1.02  --resolution_flag                       true
% 3.79/1.02  --res_lit_sel                           adaptive
% 3.79/1.02  --res_lit_sel_side                      none
% 3.79/1.02  --res_ordering                          kbo
% 3.79/1.02  --res_to_prop_solver                    active
% 3.79/1.02  --res_prop_simpl_new                    false
% 3.79/1.02  --res_prop_simpl_given                  true
% 3.79/1.02  --res_passive_queue_type                priority_queues
% 3.79/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.02  --res_passive_queues_freq               [15;5]
% 3.79/1.02  --res_forward_subs                      full
% 3.79/1.02  --res_backward_subs                     full
% 3.79/1.02  --res_forward_subs_resolution           true
% 3.79/1.02  --res_backward_subs_resolution          true
% 3.79/1.02  --res_orphan_elimination                true
% 3.79/1.02  --res_time_limit                        2.
% 3.79/1.02  --res_out_proof                         true
% 3.79/1.02  
% 3.79/1.02  ------ Superposition Options
% 3.79/1.02  
% 3.79/1.02  --superposition_flag                    true
% 3.79/1.02  --sup_passive_queue_type                priority_queues
% 3.79/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.02  --demod_completeness_check              fast
% 3.79/1.02  --demod_use_ground                      true
% 3.79/1.02  --sup_to_prop_solver                    passive
% 3.79/1.02  --sup_prop_simpl_new                    true
% 3.79/1.02  --sup_prop_simpl_given                  true
% 3.79/1.02  --sup_fun_splitting                     false
% 3.79/1.02  --sup_smt_interval                      50000
% 3.79/1.02  
% 3.79/1.02  ------ Superposition Simplification Setup
% 3.79/1.02  
% 3.79/1.02  --sup_indices_passive                   []
% 3.79/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_full_bw                           [BwDemod]
% 3.79/1.02  --sup_immed_triv                        [TrivRules]
% 3.79/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_immed_bw_main                     []
% 3.79/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.02  
% 3.79/1.02  ------ Combination Options
% 3.79/1.02  
% 3.79/1.02  --comb_res_mult                         3
% 3.79/1.02  --comb_sup_mult                         2
% 3.79/1.02  --comb_inst_mult                        10
% 3.79/1.02  
% 3.79/1.02  ------ Debug Options
% 3.79/1.02  
% 3.79/1.02  --dbg_backtrace                         false
% 3.79/1.02  --dbg_dump_prop_clauses                 false
% 3.79/1.02  --dbg_dump_prop_clauses_file            -
% 3.79/1.02  --dbg_out_stat                          false
% 3.79/1.02  ------ Parsing...
% 3.79/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.02  ------ Proving...
% 3.79/1.02  ------ Problem Properties 
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  clauses                                 26
% 3.79/1.02  conjectures                             7
% 3.79/1.02  EPR                                     3
% 3.79/1.02  Horn                                    23
% 3.79/1.02  unary                                   9
% 3.79/1.02  binary                                  7
% 3.79/1.02  lits                                    57
% 3.79/1.02  lits eq                                 25
% 3.79/1.02  fd_pure                                 0
% 3.79/1.02  fd_pseudo                               0
% 3.79/1.02  fd_cond                                 0
% 3.79/1.02  fd_pseudo_cond                          0
% 3.79/1.02  AC symbols                              0
% 3.79/1.02  
% 3.79/1.02  ------ Schedule dynamic 5 is on 
% 3.79/1.02  
% 3.79/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  ------ 
% 3.79/1.02  Current options:
% 3.79/1.02  ------ 
% 3.79/1.02  
% 3.79/1.02  ------ Input Options
% 3.79/1.02  
% 3.79/1.02  --out_options                           all
% 3.79/1.02  --tptp_safe_out                         true
% 3.79/1.02  --problem_path                          ""
% 3.79/1.02  --include_path                          ""
% 3.79/1.02  --clausifier                            res/vclausify_rel
% 3.79/1.02  --clausifier_options                    --mode clausify
% 3.79/1.02  --stdin                                 false
% 3.79/1.02  --stats_out                             all
% 3.79/1.02  
% 3.79/1.02  ------ General Options
% 3.79/1.02  
% 3.79/1.02  --fof                                   false
% 3.79/1.02  --time_out_real                         305.
% 3.79/1.02  --time_out_virtual                      -1.
% 3.79/1.02  --symbol_type_check                     false
% 3.79/1.02  --clausify_out                          false
% 3.79/1.02  --sig_cnt_out                           false
% 3.79/1.02  --trig_cnt_out                          false
% 3.79/1.02  --trig_cnt_out_tolerance                1.
% 3.79/1.02  --trig_cnt_out_sk_spl                   false
% 3.79/1.02  --abstr_cl_out                          false
% 3.79/1.02  
% 3.79/1.02  ------ Global Options
% 3.79/1.02  
% 3.79/1.02  --schedule                              default
% 3.79/1.02  --add_important_lit                     false
% 3.79/1.02  --prop_solver_per_cl                    1000
% 3.79/1.02  --min_unsat_core                        false
% 3.79/1.02  --soft_assumptions                      false
% 3.79/1.02  --soft_lemma_size                       3
% 3.79/1.02  --prop_impl_unit_size                   0
% 3.79/1.02  --prop_impl_unit                        []
% 3.79/1.02  --share_sel_clauses                     true
% 3.79/1.02  --reset_solvers                         false
% 3.79/1.02  --bc_imp_inh                            [conj_cone]
% 3.79/1.02  --conj_cone_tolerance                   3.
% 3.79/1.02  --extra_neg_conj                        none
% 3.79/1.02  --large_theory_mode                     true
% 3.79/1.02  --prolific_symb_bound                   200
% 3.79/1.02  --lt_threshold                          2000
% 3.79/1.02  --clause_weak_htbl                      true
% 3.79/1.02  --gc_record_bc_elim                     false
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing Options
% 3.79/1.02  
% 3.79/1.02  --preprocessing_flag                    true
% 3.79/1.02  --time_out_prep_mult                    0.1
% 3.79/1.02  --splitting_mode                        input
% 3.79/1.02  --splitting_grd                         true
% 3.79/1.02  --splitting_cvd                         false
% 3.79/1.02  --splitting_cvd_svl                     false
% 3.79/1.02  --splitting_nvd                         32
% 3.79/1.02  --sub_typing                            true
% 3.79/1.02  --prep_gs_sim                           true
% 3.79/1.02  --prep_unflatten                        true
% 3.79/1.02  --prep_res_sim                          true
% 3.79/1.02  --prep_upred                            true
% 3.79/1.02  --prep_sem_filter                       exhaustive
% 3.79/1.02  --prep_sem_filter_out                   false
% 3.79/1.02  --pred_elim                             true
% 3.79/1.02  --res_sim_input                         true
% 3.79/1.02  --eq_ax_congr_red                       true
% 3.79/1.02  --pure_diseq_elim                       true
% 3.79/1.02  --brand_transform                       false
% 3.79/1.02  --non_eq_to_eq                          false
% 3.79/1.02  --prep_def_merge                        true
% 3.79/1.02  --prep_def_merge_prop_impl              false
% 3.79/1.02  --prep_def_merge_mbd                    true
% 3.79/1.02  --prep_def_merge_tr_red                 false
% 3.79/1.02  --prep_def_merge_tr_cl                  false
% 3.79/1.02  --smt_preprocessing                     true
% 3.79/1.02  --smt_ac_axioms                         fast
% 3.79/1.02  --preprocessed_out                      false
% 3.79/1.02  --preprocessed_stats                    false
% 3.79/1.02  
% 3.79/1.02  ------ Abstraction refinement Options
% 3.79/1.02  
% 3.79/1.02  --abstr_ref                             []
% 3.79/1.02  --abstr_ref_prep                        false
% 3.79/1.02  --abstr_ref_until_sat                   false
% 3.79/1.02  --abstr_ref_sig_restrict                funpre
% 3.79/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.02  --abstr_ref_under                       []
% 3.79/1.02  
% 3.79/1.02  ------ SAT Options
% 3.79/1.02  
% 3.79/1.02  --sat_mode                              false
% 3.79/1.02  --sat_fm_restart_options                ""
% 3.79/1.02  --sat_gr_def                            false
% 3.79/1.02  --sat_epr_types                         true
% 3.79/1.02  --sat_non_cyclic_types                  false
% 3.79/1.02  --sat_finite_models                     false
% 3.79/1.02  --sat_fm_lemmas                         false
% 3.79/1.02  --sat_fm_prep                           false
% 3.79/1.02  --sat_fm_uc_incr                        true
% 3.79/1.02  --sat_out_model                         small
% 3.79/1.02  --sat_out_clauses                       false
% 3.79/1.02  
% 3.79/1.02  ------ QBF Options
% 3.79/1.02  
% 3.79/1.02  --qbf_mode                              false
% 3.79/1.02  --qbf_elim_univ                         false
% 3.79/1.02  --qbf_dom_inst                          none
% 3.79/1.02  --qbf_dom_pre_inst                      false
% 3.79/1.02  --qbf_sk_in                             false
% 3.79/1.02  --qbf_pred_elim                         true
% 3.79/1.02  --qbf_split                             512
% 3.79/1.02  
% 3.79/1.02  ------ BMC1 Options
% 3.79/1.02  
% 3.79/1.02  --bmc1_incremental                      false
% 3.79/1.02  --bmc1_axioms                           reachable_all
% 3.79/1.02  --bmc1_min_bound                        0
% 3.79/1.02  --bmc1_max_bound                        -1
% 3.79/1.02  --bmc1_max_bound_default                -1
% 3.79/1.02  --bmc1_symbol_reachability              true
% 3.79/1.02  --bmc1_property_lemmas                  false
% 3.79/1.02  --bmc1_k_induction                      false
% 3.79/1.02  --bmc1_non_equiv_states                 false
% 3.79/1.02  --bmc1_deadlock                         false
% 3.79/1.02  --bmc1_ucm                              false
% 3.79/1.02  --bmc1_add_unsat_core                   none
% 3.79/1.02  --bmc1_unsat_core_children              false
% 3.79/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.02  --bmc1_out_stat                         full
% 3.79/1.02  --bmc1_ground_init                      false
% 3.79/1.02  --bmc1_pre_inst_next_state              false
% 3.79/1.02  --bmc1_pre_inst_state                   false
% 3.79/1.02  --bmc1_pre_inst_reach_state             false
% 3.79/1.02  --bmc1_out_unsat_core                   false
% 3.79/1.02  --bmc1_aig_witness_out                  false
% 3.79/1.02  --bmc1_verbose                          false
% 3.79/1.02  --bmc1_dump_clauses_tptp                false
% 3.79/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.02  --bmc1_dump_file                        -
% 3.79/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.02  --bmc1_ucm_extend_mode                  1
% 3.79/1.02  --bmc1_ucm_init_mode                    2
% 3.79/1.02  --bmc1_ucm_cone_mode                    none
% 3.79/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.02  --bmc1_ucm_relax_model                  4
% 3.79/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.02  --bmc1_ucm_layered_model                none
% 3.79/1.02  --bmc1_ucm_max_lemma_size               10
% 3.79/1.02  
% 3.79/1.02  ------ AIG Options
% 3.79/1.02  
% 3.79/1.02  --aig_mode                              false
% 3.79/1.02  
% 3.79/1.02  ------ Instantiation Options
% 3.79/1.02  
% 3.79/1.02  --instantiation_flag                    true
% 3.79/1.02  --inst_sos_flag                         false
% 3.79/1.02  --inst_sos_phase                        true
% 3.79/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.02  --inst_lit_sel_side                     none
% 3.79/1.02  --inst_solver_per_active                1400
% 3.79/1.02  --inst_solver_calls_frac                1.
% 3.79/1.02  --inst_passive_queue_type               priority_queues
% 3.79/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.02  --inst_passive_queues_freq              [25;2]
% 3.79/1.02  --inst_dismatching                      true
% 3.79/1.02  --inst_eager_unprocessed_to_passive     true
% 3.79/1.02  --inst_prop_sim_given                   true
% 3.79/1.02  --inst_prop_sim_new                     false
% 3.79/1.02  --inst_subs_new                         false
% 3.79/1.02  --inst_eq_res_simp                      false
% 3.79/1.02  --inst_subs_given                       false
% 3.79/1.02  --inst_orphan_elimination               true
% 3.79/1.02  --inst_learning_loop_flag               true
% 3.79/1.02  --inst_learning_start                   3000
% 3.79/1.02  --inst_learning_factor                  2
% 3.79/1.02  --inst_start_prop_sim_after_learn       3
% 3.79/1.02  --inst_sel_renew                        solver
% 3.79/1.02  --inst_lit_activity_flag                true
% 3.79/1.02  --inst_restr_to_given                   false
% 3.79/1.02  --inst_activity_threshold               500
% 3.79/1.02  --inst_out_proof                        true
% 3.79/1.02  
% 3.79/1.02  ------ Resolution Options
% 3.79/1.02  
% 3.79/1.02  --resolution_flag                       false
% 3.79/1.02  --res_lit_sel                           adaptive
% 3.79/1.02  --res_lit_sel_side                      none
% 3.79/1.02  --res_ordering                          kbo
% 3.79/1.02  --res_to_prop_solver                    active
% 3.79/1.02  --res_prop_simpl_new                    false
% 3.79/1.02  --res_prop_simpl_given                  true
% 3.79/1.02  --res_passive_queue_type                priority_queues
% 3.79/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.02  --res_passive_queues_freq               [15;5]
% 3.79/1.02  --res_forward_subs                      full
% 3.79/1.02  --res_backward_subs                     full
% 3.79/1.02  --res_forward_subs_resolution           true
% 3.79/1.02  --res_backward_subs_resolution          true
% 3.79/1.02  --res_orphan_elimination                true
% 3.79/1.02  --res_time_limit                        2.
% 3.79/1.02  --res_out_proof                         true
% 3.79/1.02  
% 3.79/1.02  ------ Superposition Options
% 3.79/1.02  
% 3.79/1.02  --superposition_flag                    true
% 3.79/1.02  --sup_passive_queue_type                priority_queues
% 3.79/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.02  --demod_completeness_check              fast
% 3.79/1.02  --demod_use_ground                      true
% 3.79/1.02  --sup_to_prop_solver                    passive
% 3.79/1.02  --sup_prop_simpl_new                    true
% 3.79/1.02  --sup_prop_simpl_given                  true
% 3.79/1.02  --sup_fun_splitting                     false
% 3.79/1.02  --sup_smt_interval                      50000
% 3.79/1.02  
% 3.79/1.02  ------ Superposition Simplification Setup
% 3.79/1.02  
% 3.79/1.02  --sup_indices_passive                   []
% 3.79/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_full_bw                           [BwDemod]
% 3.79/1.02  --sup_immed_triv                        [TrivRules]
% 3.79/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_immed_bw_main                     []
% 3.79/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.02  
% 3.79/1.02  ------ Combination Options
% 3.79/1.02  
% 3.79/1.02  --comb_res_mult                         3
% 3.79/1.02  --comb_sup_mult                         2
% 3.79/1.02  --comb_inst_mult                        10
% 3.79/1.02  
% 3.79/1.02  ------ Debug Options
% 3.79/1.02  
% 3.79/1.02  --dbg_backtrace                         false
% 3.79/1.02  --dbg_dump_prop_clauses                 false
% 3.79/1.02  --dbg_dump_prop_clauses_file            -
% 3.79/1.02  --dbg_out_stat                          false
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  ------ Proving...
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  % SZS status Theorem for theBenchmark.p
% 3.79/1.02  
% 3.79/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.02  
% 3.79/1.02  fof(f15,conjecture,(
% 3.79/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f16,negated_conjecture,(
% 3.79/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.79/1.02    inference(negated_conjecture,[],[f15])).
% 3.79/1.02  
% 3.79/1.02  fof(f36,plain,(
% 3.79/1.02    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.79/1.02    inference(ennf_transformation,[],[f16])).
% 3.79/1.02  
% 3.79/1.02  fof(f37,plain,(
% 3.79/1.02    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.79/1.02    inference(flattening,[],[f36])).
% 3.79/1.02  
% 3.79/1.02  fof(f40,plain,(
% 3.79/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.79/1.02    introduced(choice_axiom,[])).
% 3.79/1.02  
% 3.79/1.02  fof(f39,plain,(
% 3.79/1.02    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.79/1.02    introduced(choice_axiom,[])).
% 3.79/1.02  
% 3.79/1.02  fof(f41,plain,(
% 3.79/1.02    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.79/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f40,f39])).
% 3.79/1.02  
% 3.79/1.02  fof(f64,plain,(
% 3.79/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f6,axiom,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f23,plain,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f6])).
% 3.79/1.02  
% 3.79/1.02  fof(f47,plain,(
% 3.79/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f23])).
% 3.79/1.02  
% 3.79/1.02  fof(f1,axiom,(
% 3.79/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f17,plain,(
% 3.79/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.79/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 3.79/1.02  
% 3.79/1.02  fof(f18,plain,(
% 3.79/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.79/1.02    inference(ennf_transformation,[],[f17])).
% 3.79/1.02  
% 3.79/1.02  fof(f42,plain,(
% 3.79/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f18])).
% 3.79/1.02  
% 3.79/1.02  fof(f5,axiom,(
% 3.79/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f21,plain,(
% 3.79/1.02    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.79/1.02    inference(ennf_transformation,[],[f5])).
% 3.79/1.02  
% 3.79/1.02  fof(f22,plain,(
% 3.79/1.02    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.79/1.02    inference(flattening,[],[f21])).
% 3.79/1.02  
% 3.79/1.02  fof(f46,plain,(
% 3.79/1.02    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.79/1.02    inference(cnf_transformation,[],[f22])).
% 3.79/1.02  
% 3.79/1.02  fof(f69,plain,(
% 3.79/1.02    v2_funct_1(sK4)),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f65,plain,(
% 3.79/1.02    v1_funct_1(sK4)),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f67,plain,(
% 3.79/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f2,axiom,(
% 3.79/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f19,plain,(
% 3.79/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.79/1.02    inference(ennf_transformation,[],[f2])).
% 3.79/1.02  
% 3.79/1.02  fof(f43,plain,(
% 3.79/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.79/1.02    inference(cnf_transformation,[],[f19])).
% 3.79/1.02  
% 3.79/1.02  fof(f3,axiom,(
% 3.79/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f44,plain,(
% 3.79/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f3])).
% 3.79/1.02  
% 3.79/1.02  fof(f8,axiom,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f26,plain,(
% 3.79/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f8])).
% 3.79/1.02  
% 3.79/1.02  fof(f49,plain,(
% 3.79/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f26])).
% 3.79/1.02  
% 3.79/1.02  fof(f13,axiom,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f32,plain,(
% 3.79/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f13])).
% 3.79/1.02  
% 3.79/1.02  fof(f33,plain,(
% 3.79/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(flattening,[],[f32])).
% 3.79/1.02  
% 3.79/1.02  fof(f38,plain,(
% 3.79/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(nnf_transformation,[],[f33])).
% 3.79/1.02  
% 3.79/1.02  fof(f55,plain,(
% 3.79/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f38])).
% 3.79/1.02  
% 3.79/1.02  fof(f66,plain,(
% 3.79/1.02    v1_funct_2(sK4,sK1,sK2)),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f70,plain,(
% 3.79/1.02    k1_xboole_0 != sK2),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f9,axiom,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f27,plain,(
% 3.79/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f9])).
% 3.79/1.02  
% 3.79/1.02  fof(f50,plain,(
% 3.79/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f27])).
% 3.79/1.02  
% 3.79/1.02  fof(f12,axiom,(
% 3.79/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f31,plain,(
% 3.79/1.02    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f12])).
% 3.79/1.02  
% 3.79/1.02  fof(f54,plain,(
% 3.79/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f31])).
% 3.79/1.02  
% 3.79/1.02  fof(f11,axiom,(
% 3.79/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f30,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(ennf_transformation,[],[f11])).
% 3.79/1.02  
% 3.79/1.02  fof(f52,plain,(
% 3.79/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f30])).
% 3.79/1.02  
% 3.79/1.02  fof(f10,axiom,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f28,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.79/1.02    inference(ennf_transformation,[],[f10])).
% 3.79/1.02  
% 3.79/1.02  fof(f29,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(flattening,[],[f28])).
% 3.79/1.02  
% 3.79/1.02  fof(f51,plain,(
% 3.79/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f29])).
% 3.79/1.02  
% 3.79/1.02  fof(f7,axiom,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f24,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.79/1.02    inference(ennf_transformation,[],[f7])).
% 3.79/1.02  
% 3.79/1.02  fof(f25,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.02    inference(flattening,[],[f24])).
% 3.79/1.02  
% 3.79/1.02  fof(f48,plain,(
% 3.79/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.02    inference(cnf_transformation,[],[f25])).
% 3.79/1.02  
% 3.79/1.02  fof(f14,axiom,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f34,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.79/1.02    inference(ennf_transformation,[],[f14])).
% 3.79/1.02  
% 3.79/1.02  fof(f35,plain,(
% 3.79/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.79/1.02    inference(flattening,[],[f34])).
% 3.79/1.02  
% 3.79/1.02  fof(f61,plain,(
% 3.79/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/1.02    inference(cnf_transformation,[],[f35])).
% 3.79/1.02  
% 3.79/1.02  fof(f62,plain,(
% 3.79/1.02    v1_funct_1(sK3)),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f68,plain,(
% 3.79/1.02    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  fof(f4,axiom,(
% 3.79/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.79/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.02  
% 3.79/1.02  fof(f20,plain,(
% 3.79/1.02    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.79/1.02    inference(ennf_transformation,[],[f4])).
% 3.79/1.02  
% 3.79/1.02  fof(f45,plain,(
% 3.79/1.02    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.79/1.02    inference(cnf_transformation,[],[f20])).
% 3.79/1.02  
% 3.79/1.02  fof(f71,plain,(
% 3.79/1.02    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.79/1.02    inference(cnf_transformation,[],[f41])).
% 3.79/1.02  
% 3.79/1.02  cnf(c_27,negated_conjecture,
% 3.79/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.79/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_621,negated_conjecture,
% 3.79/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_27]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1047,plain,
% 3.79/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.79/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_635,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | m1_subset_1(k2_relset_1(X1_53,X2_53,X0_53),k1_zfmisc_1(X2_53)) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1036,plain,
% 3.79/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 3.79/1.02      | m1_subset_1(k2_relset_1(X1_53,X2_53,X0_53),k1_zfmisc_1(X2_53)) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_0,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.79/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4,plain,
% 3.79/1.02      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.79/1.02      | ~ v1_funct_1(X1)
% 3.79/1.02      | ~ v2_funct_1(X1)
% 3.79/1.02      | ~ v1_relat_1(X1)
% 3.79/1.02      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.79/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_22,negated_conjecture,
% 3.79/1.02      ( v2_funct_1(sK4) ),
% 3.79/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_308,plain,
% 3.79/1.02      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.79/1.02      | ~ v1_funct_1(X1)
% 3.79/1.02      | ~ v1_relat_1(X1)
% 3.79/1.02      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.79/1.02      | sK4 != X1 ),
% 3.79/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_309,plain,
% 3.79/1.02      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.79/1.02      | ~ v1_funct_1(sK4)
% 3.79/1.02      | ~ v1_relat_1(sK4)
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.79/1.02      inference(unflattening,[status(thm)],[c_308]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_26,negated_conjecture,
% 3.79/1.02      ( v1_funct_1(sK4) ),
% 3.79/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_313,plain,
% 3.79/1.02      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.79/1.02      | ~ v1_relat_1(sK4)
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_309,c_26]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_333,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/1.02      | ~ v1_relat_1(sK4)
% 3.79/1.02      | X2 != X0
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X2)) = X2
% 3.79/1.02      | k1_relat_1(sK4) != X1 ),
% 3.79/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_313]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_334,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK4)))
% 3.79/1.02      | ~ v1_relat_1(sK4)
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.79/1.02      inference(unflattening,[status(thm)],[c_333]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_619,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4)))
% 3.79/1.02      | ~ v1_relat_1(sK4)
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53 ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_334]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1049,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
% 3.79/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 3.79/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_24,negated_conjecture,
% 3.79/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.79/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_35,plain,
% 3.79/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_702,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
% 3.79/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 3.79/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/1.02      | ~ v1_relat_1(X1)
% 3.79/1.02      | v1_relat_1(X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_638,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.79/1.02      | ~ v1_relat_1(X1_53)
% 3.79/1.02      | v1_relat_1(X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1215,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | v1_relat_1(X0_53)
% 3.79/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 3.79/1.02      inference(instantiation,[status(thm)],[c_638]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1356,plain,
% 3.79/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.79/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.79/1.02      | v1_relat_1(sK4) ),
% 3.79/1.02      inference(instantiation,[status(thm)],[c_1215]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1357,plain,
% 3.79/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.79/1.02      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.79/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.79/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_637,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1465,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.79/1.02      inference(instantiation,[status(thm)],[c_637]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1466,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5338,plain,
% 3.79/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 3.79/1.02      | k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53 ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_1049,c_35,c_702,c_1357,c_1466]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5339,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
% 3.79/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
% 3.79/1.02      inference(renaming,[status(thm)],[c_5338]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_623,negated_conjecture,
% 3.79/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_24]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1045,plain,
% 3.79/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_7,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_633,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1038,plain,
% 3.79/1.02      ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1376,plain,
% 3.79/1.02      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1038]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_18,plain,
% 3.79/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.79/1.02      | k1_xboole_0 = X2 ),
% 3.79/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_25,negated_conjecture,
% 3.79/1.02      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.79/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_426,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.79/1.02      | sK4 != X0
% 3.79/1.02      | sK2 != X2
% 3.79/1.02      | sK1 != X1
% 3.79/1.02      | k1_xboole_0 = X2 ),
% 3.79/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_427,plain,
% 3.79/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.79/1.02      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.79/1.02      | k1_xboole_0 = sK2 ),
% 3.79/1.02      inference(unflattening,[status(thm)],[c_426]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_21,negated_conjecture,
% 3.79/1.02      ( k1_xboole_0 != sK2 ),
% 3.79/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_429,plain,
% 3.79/1.02      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_427,c_24,c_21]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_614,plain,
% 3.79/1.02      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_429]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1381,plain,
% 3.79/1.02      ( k1_relat_1(sK4) = sK1 ),
% 3.79/1.02      inference(light_normalisation,[status(thm)],[c_1376,c_614]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5344,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,X0_53)) = X0_53
% 3.79/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.79/1.02      inference(light_normalisation,[status(thm)],[c_5339,c_1381]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5350,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relset_1(X0_53,sK1,X1_53))) = k2_relset_1(X0_53,sK1,X1_53)
% 3.79/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1036,c_5344]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_7755,plain,
% 3.79/1.02      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relset_1(sK0,sK1,sK3))) = k2_relset_1(sK0,sK1,sK3) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1047,c_5350]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_8,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_632,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1039,plain,
% 3.79/1.02      ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1387,plain,
% 3.79/1.02      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1047,c_1039]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_11,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_629,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | k8_relset_1(X1_53,X2_53,X0_53,X2_53) = k1_relset_1(X1_53,X2_53,X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1042,plain,
% 3.79/1.02      ( k8_relset_1(X0_53,X1_53,X2_53,X1_53) = k1_relset_1(X0_53,X1_53,X2_53)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2240,plain,
% 3.79/1.02      ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1042]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2251,plain,
% 3.79/1.02      ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
% 3.79/1.02      inference(light_normalisation,[status(thm)],[c_2240,c_614]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_10,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.79/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_630,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1041,plain,
% 3.79/1.02      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2221,plain,
% 3.79/1.02      ( k8_relset_1(sK1,sK2,sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1041]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2699,plain,
% 3.79/1.02      ( k10_relat_1(sK4,sK2) = sK1 ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_2251,c_2221]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_9,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.79/1.02      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_631,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
% 3.79/1.02      | k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1040,plain,
% 3.79/1.02      ( k4_relset_1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
% 3.79/1.02      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 3.79/1.02      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4066,plain,
% 3.79/1.02      ( k4_relset_1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1040]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4750,plain,
% 3.79/1.02      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1047,c_4066]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_6,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.79/1.02      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.79/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_634,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
% 3.79/1.02      | m1_subset_1(k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1037,plain,
% 3.79/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 3.79/1.02      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53))) != iProver_top
% 3.79/1.02      | m1_subset_1(k4_relset_1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4796,plain,
% 3.79/1.02      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.79/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.79/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_4750,c_1037]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_32,plain,
% 3.79/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_6078,plain,
% 3.79/1.02      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_4796,c_32,c_35]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_6094,plain,
% 3.79/1.02      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_6078,c_1039]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_19,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.79/1.02      | ~ v1_funct_1(X0)
% 3.79/1.02      | ~ v1_funct_1(X3)
% 3.79/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.79/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_627,plain,
% 3.79/1.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.79/1.02      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
% 3.79/1.02      | ~ v1_funct_1(X0_53)
% 3.79/1.02      | ~ v1_funct_1(X3_53)
% 3.79/1.02      | k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1044,plain,
% 3.79/1.02      ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
% 3.79/1.02      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 3.79/1.02      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.79/1.02      | v1_funct_1(X5_53) != iProver_top
% 3.79/1.02      | v1_funct_1(X4_53) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4456,plain,
% 3.79/1.02      ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.79/1.02      | v1_funct_1(X2_53) != iProver_top
% 3.79/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1044]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_33,plain,
% 3.79/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5278,plain,
% 3.79/1.02      ( v1_funct_1(X2_53) != iProver_top
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.79/1.02      | k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4) ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_4456,c_33]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5279,plain,
% 3.79/1.02      ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
% 3.79/1.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.79/1.02      | v1_funct_1(X2_53) != iProver_top ),
% 3.79/1.02      inference(renaming,[status(thm)],[c_5278]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5288,plain,
% 3.79/1.02      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.79/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1047,c_5279]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_29,negated_conjecture,
% 3.79/1.02      ( v1_funct_1(sK3) ),
% 3.79/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_30,plain,
% 3.79/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5436,plain,
% 3.79/1.02      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_5288,c_30]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_23,negated_conjecture,
% 3.79/1.02      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.79/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_624,negated_conjecture,
% 3.79/1.02      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_5440,plain,
% 3.79/1.02      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.79/1.02      inference(demodulation,[status(thm)],[c_5436,c_624]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_6099,plain,
% 3.79/1.02      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.79/1.02      inference(light_normalisation,[status(thm)],[c_6094,c_5440]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1033,plain,
% 3.79/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 3.79/1.02      | v1_relat_1(X1_53) != iProver_top
% 3.79/1.02      | v1_relat_1(X0_53) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1508,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.79/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1047,c_1033]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1359,plain,
% 3.79/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.79/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.79/1.02      | v1_relat_1(sK3) ),
% 3.79/1.02      inference(instantiation,[status(thm)],[c_1215]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1360,plain,
% 3.79/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.79/1.02      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.79/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_1359]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1468,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.79/1.02      inference(instantiation,[status(thm)],[c_637]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1469,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1847,plain,
% 3.79/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_1508,c_32,c_1360,c_1469]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1507,plain,
% 3.79/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.79/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1045,c_1033]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1841,plain,
% 3.79/1.02      ( v1_relat_1(sK4) = iProver_top ),
% 3.79/1.02      inference(global_propositional_subsumption,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_1507,c_35,c_1357,c_1466]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_3,plain,
% 3.79/1.02      ( ~ v1_relat_1(X0)
% 3.79/1.02      | ~ v1_relat_1(X1)
% 3.79/1.02      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 3.79/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_636,plain,
% 3.79/1.02      ( ~ v1_relat_1(X0_53)
% 3.79/1.02      | ~ v1_relat_1(X1_53)
% 3.79/1.02      | k9_relat_1(X1_53,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,X1_53)) ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1035,plain,
% 3.79/1.02      ( k9_relat_1(X0_53,k2_relat_1(X1_53)) = k2_relat_1(k5_relat_1(X1_53,X0_53))
% 3.79/1.02      | v1_relat_1(X1_53) != iProver_top
% 3.79/1.02      | v1_relat_1(X0_53) != iProver_top ),
% 3.79/1.02      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_2522,plain,
% 3.79/1.02      ( k9_relat_1(sK4,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,sK4))
% 3.79/1.02      | v1_relat_1(X0_53) != iProver_top ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1841,c_1035]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_4515,plain,
% 3.79/1.02      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.79/1.02      inference(superposition,[status(thm)],[c_1847,c_2522]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_6151,plain,
% 3.79/1.02      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 3.79/1.02      inference(demodulation,[status(thm)],[c_6099,c_4515]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_7775,plain,
% 3.79/1.02      ( k2_relat_1(sK3) = sK1 ),
% 3.79/1.02      inference(light_normalisation,
% 3.79/1.02                [status(thm)],
% 3.79/1.02                [c_7755,c_1387,c_2699,c_6151]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_20,negated_conjecture,
% 3.79/1.02      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.79/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_626,negated_conjecture,
% 3.79/1.02      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.79/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(c_1618,plain,
% 3.79/1.02      ( k2_relat_1(sK3) != sK1 ),
% 3.79/1.02      inference(demodulation,[status(thm)],[c_1387,c_626]) ).
% 3.79/1.02  
% 3.79/1.02  cnf(contradiction,plain,
% 3.79/1.02      ( $false ),
% 3.79/1.02      inference(minisat,[status(thm)],[c_7775,c_1618]) ).
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.02  
% 3.79/1.02  ------                               Statistics
% 3.79/1.02  
% 3.79/1.02  ------ General
% 3.79/1.02  
% 3.79/1.02  abstr_ref_over_cycles:                  0
% 3.79/1.02  abstr_ref_under_cycles:                 0
% 3.79/1.02  gc_basic_clause_elim:                   0
% 3.79/1.02  forced_gc_time:                         0
% 3.79/1.02  parsing_time:                           0.009
% 3.79/1.02  unif_index_cands_time:                  0.
% 3.79/1.02  unif_index_add_time:                    0.
% 3.79/1.02  orderings_time:                         0.
% 3.79/1.02  out_proof_time:                         0.01
% 3.79/1.02  total_time:                             0.318
% 3.79/1.02  num_of_symbols:                         58
% 3.79/1.02  num_of_terms:                           8959
% 3.79/1.02  
% 3.79/1.02  ------ Preprocessing
% 3.79/1.02  
% 3.79/1.02  num_of_splits:                          0
% 3.79/1.02  num_of_split_atoms:                     0
% 3.79/1.02  num_of_reused_defs:                     0
% 3.79/1.02  num_eq_ax_congr_red:                    54
% 3.79/1.02  num_of_sem_filtered_clauses:            1
% 3.79/1.02  num_of_subtypes:                        2
% 3.79/1.02  monotx_restored_types:                  0
% 3.79/1.02  sat_num_of_epr_types:                   0
% 3.79/1.02  sat_num_of_non_cyclic_types:            0
% 3.79/1.02  sat_guarded_non_collapsed_types:        1
% 3.79/1.02  num_pure_diseq_elim:                    0
% 3.79/1.02  simp_replaced_by:                       0
% 3.79/1.02  res_preprocessed:                       139
% 3.79/1.02  prep_upred:                             0
% 3.79/1.02  prep_unflattend:                        37
% 3.79/1.02  smt_new_axioms:                         0
% 3.79/1.02  pred_elim_cands:                        3
% 3.79/1.02  pred_elim:                              3
% 3.79/1.02  pred_elim_cl:                           4
% 3.79/1.02  pred_elim_cycles:                       5
% 3.79/1.02  merged_defs:                            0
% 3.79/1.02  merged_defs_ncl:                        0
% 3.79/1.02  bin_hyper_res:                          0
% 3.79/1.02  prep_cycles:                            4
% 3.79/1.02  pred_elim_time:                         0.005
% 3.79/1.02  splitting_time:                         0.
% 3.79/1.02  sem_filter_time:                        0.
% 3.79/1.02  monotx_time:                            0.
% 3.79/1.02  subtype_inf_time:                       0.
% 3.79/1.02  
% 3.79/1.02  ------ Problem properties
% 3.79/1.02  
% 3.79/1.02  clauses:                                26
% 3.79/1.02  conjectures:                            7
% 3.79/1.02  epr:                                    3
% 3.79/1.02  horn:                                   23
% 3.79/1.02  ground:                                 13
% 3.79/1.02  unary:                                  9
% 3.79/1.02  binary:                                 7
% 3.79/1.02  lits:                                   57
% 3.79/1.02  lits_eq:                                25
% 3.79/1.02  fd_pure:                                0
% 3.79/1.02  fd_pseudo:                              0
% 3.79/1.02  fd_cond:                                0
% 3.79/1.02  fd_pseudo_cond:                         0
% 3.79/1.02  ac_symbols:                             0
% 3.79/1.02  
% 3.79/1.02  ------ Propositional Solver
% 3.79/1.02  
% 3.79/1.02  prop_solver_calls:                      27
% 3.79/1.02  prop_fast_solver_calls:                 987
% 3.79/1.02  smt_solver_calls:                       0
% 3.79/1.02  smt_fast_solver_calls:                  0
% 3.79/1.02  prop_num_of_clauses:                    3231
% 3.79/1.02  prop_preprocess_simplified:             7445
% 3.79/1.02  prop_fo_subsumed:                       32
% 3.79/1.02  prop_solver_time:                       0.
% 3.79/1.02  smt_solver_time:                        0.
% 3.79/1.02  smt_fast_solver_time:                   0.
% 3.79/1.02  prop_fast_solver_time:                  0.
% 3.79/1.02  prop_unsat_core_time:                   0.
% 3.79/1.02  
% 3.79/1.02  ------ QBF
% 3.79/1.02  
% 3.79/1.02  qbf_q_res:                              0
% 3.79/1.02  qbf_num_tautologies:                    0
% 3.79/1.02  qbf_prep_cycles:                        0
% 3.79/1.02  
% 3.79/1.02  ------ BMC1
% 3.79/1.02  
% 3.79/1.02  bmc1_current_bound:                     -1
% 3.79/1.02  bmc1_last_solved_bound:                 -1
% 3.79/1.02  bmc1_unsat_core_size:                   -1
% 3.79/1.02  bmc1_unsat_core_parents_size:           -1
% 3.79/1.02  bmc1_merge_next_fun:                    0
% 3.79/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.02  
% 3.79/1.02  ------ Instantiation
% 3.79/1.02  
% 3.79/1.02  inst_num_of_clauses:                    907
% 3.79/1.02  inst_num_in_passive:                    66
% 3.79/1.02  inst_num_in_active:                     732
% 3.79/1.02  inst_num_in_unprocessed:                109
% 3.79/1.02  inst_num_of_loops:                      780
% 3.79/1.02  inst_num_of_learning_restarts:          0
% 3.79/1.02  inst_num_moves_active_passive:          46
% 3.79/1.02  inst_lit_activity:                      0
% 3.79/1.02  inst_lit_activity_moves:                1
% 3.79/1.02  inst_num_tautologies:                   0
% 3.79/1.02  inst_num_prop_implied:                  0
% 3.79/1.02  inst_num_existing_simplified:           0
% 3.79/1.02  inst_num_eq_res_simplified:             0
% 3.79/1.02  inst_num_child_elim:                    0
% 3.79/1.02  inst_num_of_dismatching_blockings:      330
% 3.79/1.02  inst_num_of_non_proper_insts:           559
% 3.79/1.02  inst_num_of_duplicates:                 0
% 3.79/1.02  inst_inst_num_from_inst_to_res:         0
% 3.79/1.02  inst_dismatching_checking_time:         0.
% 3.79/1.02  
% 3.79/1.02  ------ Resolution
% 3.79/1.02  
% 3.79/1.02  res_num_of_clauses:                     0
% 3.79/1.02  res_num_in_passive:                     0
% 3.79/1.02  res_num_in_active:                      0
% 3.79/1.02  res_num_of_loops:                       143
% 3.79/1.02  res_forward_subset_subsumed:            90
% 3.79/1.02  res_backward_subset_subsumed:           0
% 3.79/1.02  res_forward_subsumed:                   0
% 3.79/1.02  res_backward_subsumed:                  0
% 3.79/1.02  res_forward_subsumption_resolution:     0
% 3.79/1.02  res_backward_subsumption_resolution:    0
% 3.79/1.02  res_clause_to_clause_subsumption:       603
% 3.79/1.02  res_orphan_elimination:                 0
% 3.79/1.02  res_tautology_del:                      19
% 3.79/1.02  res_num_eq_res_simplified:              0
% 3.79/1.02  res_num_sel_changes:                    0
% 3.79/1.02  res_moves_from_active_to_pass:          0
% 3.79/1.02  
% 3.79/1.02  ------ Superposition
% 3.79/1.02  
% 3.79/1.02  sup_time_total:                         0.
% 3.79/1.02  sup_time_generating:                    0.
% 3.79/1.02  sup_time_sim_full:                      0.
% 3.79/1.02  sup_time_sim_immed:                     0.
% 3.79/1.02  
% 3.79/1.02  sup_num_of_clauses:                     304
% 3.79/1.02  sup_num_in_active:                      151
% 3.79/1.02  sup_num_in_passive:                     153
% 3.79/1.02  sup_num_of_loops:                       154
% 3.79/1.02  sup_fw_superposition:                   183
% 3.79/1.02  sup_bw_superposition:                   119
% 3.79/1.02  sup_immediate_simplified:               58
% 3.79/1.02  sup_given_eliminated:                   0
% 3.79/1.02  comparisons_done:                       0
% 3.79/1.02  comparisons_avoided:                    3
% 3.79/1.02  
% 3.79/1.02  ------ Simplifications
% 3.79/1.02  
% 3.79/1.02  
% 3.79/1.02  sim_fw_subset_subsumed:                 4
% 3.79/1.02  sim_bw_subset_subsumed:                 0
% 3.79/1.02  sim_fw_subsumed:                        0
% 3.79/1.02  sim_bw_subsumed:                        0
% 3.79/1.02  sim_fw_subsumption_res:                 1
% 3.79/1.02  sim_bw_subsumption_res:                 0
% 3.79/1.02  sim_tautology_del:                      2
% 3.79/1.02  sim_eq_tautology_del:                   8
% 3.79/1.02  sim_eq_res_simp:                        0
% 3.79/1.02  sim_fw_demodulated:                     0
% 3.79/1.02  sim_bw_demodulated:                     4
% 3.79/1.02  sim_light_normalised:                   55
% 3.79/1.02  sim_joinable_taut:                      0
% 3.79/1.02  sim_joinable_simp:                      0
% 3.79/1.02  sim_ac_normalised:                      0
% 3.79/1.02  sim_smt_subsumption:                    0
% 3.79/1.02  
%------------------------------------------------------------------------------
