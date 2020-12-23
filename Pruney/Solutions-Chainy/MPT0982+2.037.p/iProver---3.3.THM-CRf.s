%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:44 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 539 expanded)
%              Number of clauses        :  109 ( 201 expanded)
%              Number of leaves         :   17 ( 120 expanded)
%              Depth                    :   22
%              Number of atoms          :  504 (3360 expanded)
%              Number of equality atoms :  230 (1126 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f41,f40])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f51,plain,(
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

fof(f39,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

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

fof(f56,plain,(
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

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_647,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1055,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_649,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1053,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
    | m1_subset_1(k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1045,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54))) != iProver_top
    | m1_subset_1(k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k2_relset_1(X1_54,X2_54,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1047,plain,
    ( k2_relset_1(X0_54,X1_54,X2_54) = k2_relat_1(X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2055,plain,
    ( k2_relset_1(X0_54,X1_54,k4_relset_1(X0_54,X2_54,X3_54,X1_54,X4_54,X5_54)) = k2_relat_1(k4_relset_1(X0_54,X2_54,X3_54,X1_54,X4_54,X5_54))
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1047])).

cnf(c_4993,plain,
    ( k2_relset_1(X0_54,sK2,k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4)) = k2_relat_1(k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4))
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_2055])).

cnf(c_5172,plain,
    ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1055,c_4993])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
    | k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54) = k5_relat_1(X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1048,plain,
    ( k4_relset_1(X0_54,X1_54,X2_54,X3_54,X4_54,X5_54) = k5_relat_1(X4_54,X5_54)
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_3575,plain,
    ( k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1048])).

cnf(c_4081,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1055,c_3575])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | k1_partfun1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54) = k5_relat_1(X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1052,plain,
    ( k1_partfun1(X0_54,X1_54,X2_54,X3_54,X4_54,X5_54) = k5_relat_1(X4_54,X5_54)
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_3609,plain,
    ( k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1052])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4200,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_34])).

cnf(c_4201,plain,
    ( k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4200])).

cnf(c_4210,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_4201])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4674,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4210,c_31])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_650,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4677,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4674,c_650])).

cnf(c_5185,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5172,c_4081,c_4677])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1042,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_1447,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1042])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1219,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X1_54,X2_54)) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1352,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_662,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1417,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1418,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_1925,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_33,c_1352,c_1418])).

cnf(c_1446,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1042])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1349,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1348])).

cnf(c_1414,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1415,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1414])).

cnf(c_1919,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_36,c_1349,c_1415])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_661,plain,
    ( ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | k9_relat_1(X1_54,k2_relat_1(X0_54)) = k2_relat_1(k5_relat_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1044,plain,
    ( k9_relat_1(X0_54,k2_relat_1(X1_54)) = k2_relat_1(k5_relat_1(X1_54,X0_54))
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2349,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0_54)) = k2_relat_1(k5_relat_1(X0_54,sK4))
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1919,c_1044])).

cnf(c_3938,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1925,c_2349])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_343,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_27])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
    | k1_relat_1(sK4) != X2
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_323])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK4))))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0))) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4))))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_1057,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_726,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_4630,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1057,c_36,c_726,c_1349,c_1415])).

cnf(c_4631,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4630])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k1_relset_1(X1_54,X2_54,X0_54) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1046,plain,
    ( k1_relset_1(X0_54,X1_54,X2_54) = k1_relat_1(X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_1383,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1053,c_1046])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_462,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_25,c_22])).

cnf(c_640,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(subtyping,[status(esa)],[c_462])).

cnf(c_1388,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1383,c_640])).

cnf(c_4636,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4631,c_1388])).

cnf(c_4643,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_4636])).

cnf(c_4666,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_33,c_1352,c_1418])).

cnf(c_4924,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3938,c_4666])).

cnf(c_5193,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5185,c_4924])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k8_relset_1(X1_54,X2_54,X0_54,X2_54) = k1_relset_1(X1_54,X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1050,plain,
    ( k8_relset_1(X0_54,X1_54,X2_54,X1_54) = k1_relset_1(X0_54,X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_2208,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1053,c_1050])).

cnf(c_2221,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2208,c_640])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k8_relset_1(X1_54,X2_54,X0_54,X3_54) = k10_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1049,plain,
    ( k8_relset_1(X0_54,X1_54,X2_54,X3_54) = k10_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_2187,plain,
    ( k8_relset_1(sK1,sK2,sK4,X0_54) = k10_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1053,c_1049])).

cnf(c_2398,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_2221,c_2187])).

cnf(c_5198,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5193,c_2398])).

cnf(c_1394,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1055,c_1047])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_652,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1714,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1394,c_652])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5198,c_1714])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.04/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.98  
% 3.04/0.98  ------  iProver source info
% 3.04/0.98  
% 3.04/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.98  git: non_committed_changes: false
% 3.04/0.98  git: last_make_outside_of_git: false
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     num_symb
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       true
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  ------ Parsing...
% 3.04/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.98  ------ Proving...
% 3.04/0.98  ------ Problem Properties 
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  clauses                                 25
% 3.04/0.98  conjectures                             7
% 3.04/0.98  EPR                                     3
% 3.04/0.98  Horn                                    22
% 3.04/0.98  unary                                   9
% 3.04/0.98  binary                                  6
% 3.04/0.98  lits                                    56
% 3.04/0.98  lits eq                                 25
% 3.04/0.98  fd_pure                                 0
% 3.04/0.98  fd_pseudo                               0
% 3.04/0.98  fd_cond                                 0
% 3.04/0.98  fd_pseudo_cond                          0
% 3.04/0.98  AC symbols                              0
% 3.04/0.98  
% 3.04/0.98  ------ Schedule dynamic 5 is on 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  Current options:
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     none
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       false
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ Proving...
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  % SZS status Theorem for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  fof(f15,conjecture,(
% 3.04/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f16,negated_conjecture,(
% 3.04/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.04/0.98    inference(negated_conjecture,[],[f15])).
% 3.04/0.98  
% 3.04/0.98  fof(f36,plain,(
% 3.04/0.98    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.04/0.98    inference(ennf_transformation,[],[f16])).
% 3.04/0.98  
% 3.04/0.98  fof(f37,plain,(
% 3.04/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.04/0.98    inference(flattening,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f41,plain,(
% 3.04/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f40,plain,(
% 3.04/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f42,plain,(
% 3.04/0.98    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f41,f40])).
% 3.04/0.98  
% 3.04/0.98  fof(f66,plain,(
% 3.04/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.04/0.98    inference(cnf_transformation,[],[f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f69,plain,(
% 3.04/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.04/0.98    inference(cnf_transformation,[],[f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f7,axiom,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f24,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.04/0.98    inference(ennf_transformation,[],[f7])).
% 3.04/0.98  
% 3.04/0.98  fof(f25,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(flattening,[],[f24])).
% 3.04/0.98  
% 3.04/0.98  fof(f50,plain,(
% 3.04/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f25])).
% 3.04/0.98  
% 3.04/0.98  fof(f9,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f27,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f9])).
% 3.04/0.98  
% 3.04/0.98  fof(f52,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f27])).
% 3.04/0.98  
% 3.04/0.98  fof(f10,axiom,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f28,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.04/0.98    inference(ennf_transformation,[],[f10])).
% 3.04/0.98  
% 3.04/0.98  fof(f29,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(flattening,[],[f28])).
% 3.04/0.98  
% 3.04/0.98  fof(f53,plain,(
% 3.04/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f29])).
% 3.04/0.98  
% 3.04/0.98  fof(f14,axiom,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f34,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.04/0.98    inference(ennf_transformation,[],[f14])).
% 3.04/0.98  
% 3.04/0.98  fof(f35,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.04/0.98    inference(flattening,[],[f34])).
% 3.04/0.98  
% 3.04/0.98  fof(f63,plain,(
% 3.04/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f35])).
% 3.04/0.98  
% 3.04/0.98  fof(f67,plain,(
% 3.04/0.98    v1_funct_1(sK4)),
% 3.04/0.98    inference(cnf_transformation,[],[f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f64,plain,(
% 3.04/0.98    v1_funct_1(sK3)),
% 3.04/0.98    inference(cnf_transformation,[],[f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f70,plain,(
% 3.04/0.98    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.04/0.98    inference(cnf_transformation,[],[f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f1,axiom,(
% 3.04/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f18,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.04/0.98    inference(ennf_transformation,[],[f1])).
% 3.04/0.98  
% 3.04/0.98  fof(f43,plain,(
% 3.04/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f18])).
% 3.04/0.98  
% 3.04/0.98  fof(f3,axiom,(
% 3.04/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f46,plain,(
% 3.04/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f3])).
% 3.04/0.98  
% 3.04/0.98  fof(f4,axiom,(
% 3.04/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f20,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.04/0.98    inference(ennf_transformation,[],[f4])).
% 3.04/0.98  
% 3.04/0.98  fof(f47,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f20])).
% 3.04/0.98  
% 3.04/0.98  fof(f6,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f17,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.04/0.98    inference(pure_predicate_removal,[],[f6])).
% 3.04/0.98  
% 3.04/0.98  fof(f23,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f17])).
% 3.04/0.98  
% 3.04/0.98  fof(f49,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f23])).
% 3.04/0.98  
% 3.04/0.98  fof(f2,axiom,(
% 3.04/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f19,plain,(
% 3.04/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.04/0.98    inference(ennf_transformation,[],[f2])).
% 3.04/0.98  
% 3.04/0.98  fof(f38,plain,(
% 3.04/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.04/0.98    inference(nnf_transformation,[],[f19])).
% 3.04/0.98  
% 3.04/0.98  fof(f44,plain,(
% 3.04/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f21,plain,(
% 3.04/0.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,plain,(
% 3.04/0.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(flattening,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f71,plain,(
% 3.04/0.99    v2_funct_1(sK4)),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f26,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f8])).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f26])).
% 3.04/0.99  
% 3.04/0.99  fof(f13,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f13])).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(flattening,[],[f32])).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(nnf_transformation,[],[f33])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f68,plain,(
% 3.04/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f72,plain,(
% 3.04/0.99    k1_xboole_0 != sK2),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f56,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f73,plain,(
% 3.04/0.99    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_28,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_647,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1055,plain,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_25,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_649,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1053,plain,
% 3.04/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.04/0.99      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_660,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
% 3.04/0.99      | m1_subset_1(k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1045,plain,
% 3.04/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 3.04/0.99      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54))) != iProver_top
% 3.04/0.99      | m1_subset_1(k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_658,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | k2_relset_1(X1_54,X2_54,X0_54) = k2_relat_1(X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1047,plain,
% 3.04/0.99      ( k2_relset_1(X0_54,X1_54,X2_54) = k2_relat_1(X2_54)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2055,plain,
% 3.04/0.99      ( k2_relset_1(X0_54,X1_54,k4_relset_1(X0_54,X2_54,X3_54,X1_54,X4_54,X5_54)) = k2_relat_1(k4_relset_1(X0_54,X2_54,X3_54,X1_54,X4_54,X5_54))
% 3.04/0.99      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
% 3.04/0.99      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1045,c_1047]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4993,plain,
% 3.04/0.99      ( k2_relset_1(X0_54,sK2,k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4)) = k2_relat_1(k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4))
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_2055]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5172,plain,
% 3.04/0.99      ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_4993]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_10,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.04/0.99      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_657,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
% 3.04/0.99      | k4_relset_1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54) = k5_relat_1(X3_54,X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1048,plain,
% 3.04/0.99      ( k4_relset_1(X0_54,X1_54,X2_54,X3_54,X4_54,X5_54) = k5_relat_1(X4_54,X5_54)
% 3.04/0.99      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 3.04/0.99      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3575,plain,
% 3.04/0.99      ( k4_relset_1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1048]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4081,plain,
% 3.04/0.99      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_3575]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_20,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X3)
% 3.04/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_653,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X5_54)))
% 3.04/0.99      | ~ v1_funct_1(X0_54)
% 3.04/0.99      | ~ v1_funct_1(X3_54)
% 3.04/0.99      | k1_partfun1(X4_54,X5_54,X1_54,X2_54,X3_54,X0_54) = k5_relat_1(X3_54,X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1052,plain,
% 3.04/0.99      ( k1_partfun1(X0_54,X1_54,X2_54,X3_54,X4_54,X5_54) = k5_relat_1(X4_54,X5_54)
% 3.04/0.99      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 3.04/0.99      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.04/0.99      | v1_funct_1(X5_54) != iProver_top
% 3.04/0.99      | v1_funct_1(X4_54) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3609,plain,
% 3.04/0.99      ( k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.04/0.99      | v1_funct_1(X2_54) != iProver_top
% 3.04/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1052]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK4) ),
% 3.04/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_34,plain,
% 3.04/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4200,plain,
% 3.04/0.99      ( v1_funct_1(X2_54) != iProver_top
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.04/0.99      | k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_3609,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4201,plain,
% 3.04/0.99      ( k1_partfun1(X0_54,X1_54,sK1,sK2,X2_54,sK4) = k5_relat_1(X2_54,sK4)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.04/0.99      | v1_funct_1(X2_54) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_4200]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4210,plain,
% 3.04/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.04/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_4201]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_30,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_31,plain,
% 3.04/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4674,plain,
% 3.04/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4210,c_31]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_24,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_650,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4677,plain,
% 3.04/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_4674,c_650]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5185,plain,
% 3.04/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_5172,c_4081,c_4677]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_663,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.04/0.99      | ~ v1_relat_1(X1_54)
% 3.04/0.99      | v1_relat_1(X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1042,plain,
% 3.04/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 3.04/0.99      | v1_relat_1(X1_54) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1447,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_1042]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,plain,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1219,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | v1_relat_1(X0_54)
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_54,X2_54)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_663]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1351,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.04/0.99      | v1_relat_1(sK3) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1352,plain,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_662,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1417,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_662]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1418,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1925,plain,
% 3.04/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1447,c_33,c_1352,c_1418]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1446,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1042]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_36,plain,
% 3.04/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1348,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.04/0.99      | v1_relat_1(sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1349,plain,
% 3.04/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1348]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1414,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_662]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1415,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1414]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1919,plain,
% 3.04/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1446,c_36,c_1349,c_1415]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_661,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0_54)
% 3.04/0.99      | ~ v1_relat_1(X1_54)
% 3.04/0.99      | k9_relat_1(X1_54,k2_relat_1(X0_54)) = k2_relat_1(k5_relat_1(X0_54,X1_54)) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1044,plain,
% 3.04/0.99      ( k9_relat_1(X0_54,k2_relat_1(X1_54)) = k2_relat_1(k5_relat_1(X1_54,X0_54))
% 3.04/0.99      | v1_relat_1(X1_54) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2349,plain,
% 3.04/0.99      ( k9_relat_1(sK4,k2_relat_1(X0_54)) = k2_relat_1(k5_relat_1(X0_54,sK4))
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1919,c_1044]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3938,plain,
% 3.04/0.99      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1925,c_2349]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,plain,
% 3.04/0.99      ( v5_relat_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2,plain,
% 3.04/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v5_relat_1(X0,X1)
% 3.04/0.99      | ~ v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_343,plain,
% 3.04/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.04/0.99      | ~ v1_relat_1(X0) ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_6,c_2]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.04/0.99      | ~ v1_funct_1(X1)
% 3.04/0.99      | ~ v2_funct_1(X1)
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_23,negated_conjecture,
% 3.04/0.99      ( v2_funct_1(sK4) ),
% 3.04/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_318,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.04/0.99      | ~ v1_funct_1(X1)
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.04/0.99      | sK4 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_319,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.04/0.99      | ~ v1_funct_1(sK4)
% 3.04/0.99      | ~ v1_relat_1(sK4)
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_318]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_323,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.04/0.99      | ~ v1_relat_1(sK4)
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_319,c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_362,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(sK4)
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
% 3.04/0.99      | k1_relat_1(sK4) != X2
% 3.04/0.99      | k2_relat_1(X0) != X3 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_343,c_323]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_363,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK4))))
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(sK4)
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0))) = k2_relat_1(X0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_645,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4))))
% 3.04/0.99      | ~ v1_relat_1(X0_54)
% 3.04/0.99      | ~ v1_relat_1(sK4)
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_363]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1057,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
% 3.04/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top
% 3.04/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_726,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
% 3.04/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top
% 3.04/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4630,plain,
% 3.04/0.99      ( v1_relat_1(X0_54) != iProver_top
% 3.04/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
% 3.04/0.99      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1057,c_36,c_726,c_1349,c_1415]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4631,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
% 3.04/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,k1_relat_1(sK4)))) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_4630]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_659,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | k1_relset_1(X1_54,X2_54,X0_54) = k1_relat_1(X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1046,plain,
% 3.04/0.99      ( k1_relset_1(X0_54,X1_54,X2_54) = k1_relat_1(X2_54)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1383,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1046]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_19,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_26,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_459,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | sK4 != X0
% 3.04/0.99      | sK2 != X2
% 3.04/0.99      | sK1 != X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_460,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.04/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.04/0.99      | k1_xboole_0 = sK2 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,negated_conjecture,
% 3.04/0.99      ( k1_xboole_0 != sK2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_462,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_460,c_25,c_22]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_640,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_462]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1388,plain,
% 3.04/0.99      ( k1_relat_1(sK4) = sK1 ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1383,c_640]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4636,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_54))) = k2_relat_1(X0_54)
% 3.04/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 3.04/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_4631,c_1388]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4643,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
% 3.04/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_4636]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4666,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4643,c_33,c_1352,c_1418]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4924,plain,
% 3.04/0.99      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3938,c_4666]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5193,plain,
% 3.04/0.99      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_5185,c_4924]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_12,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_655,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | k8_relset_1(X1_54,X2_54,X0_54,X2_54) = k1_relset_1(X1_54,X2_54,X0_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1050,plain,
% 3.04/0.99      ( k8_relset_1(X0_54,X1_54,X2_54,X1_54) = k1_relset_1(X0_54,X1_54,X2_54)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2208,plain,
% 3.04/0.99      ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1050]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2221,plain,
% 3.04/0.99      ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_2208,c_640]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_11,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_656,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.04/0.99      | k8_relset_1(X1_54,X2_54,X0_54,X3_54) = k10_relat_1(X0_54,X3_54) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1049,plain,
% 3.04/0.99      ( k8_relset_1(X0_54,X1_54,X2_54,X3_54) = k10_relat_1(X2_54,X3_54)
% 3.04/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2187,plain,
% 3.04/0.99      ( k8_relset_1(sK1,sK2,sK4,X0_54) = k10_relat_1(sK4,X0_54) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1053,c_1049]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2398,plain,
% 3.04/0.99      ( k10_relat_1(sK4,sK2) = sK1 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2221,c_2187]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5198,plain,
% 3.04/0.99      ( k2_relat_1(sK3) = sK1 ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_5193,c_2398]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1394,plain,
% 3.04/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1055,c_1047]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_21,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.04/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_652,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1714,plain,
% 3.04/0.99      ( k2_relat_1(sK3) != sK1 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1394,c_652]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,[status(thm)],[c_5198,c_1714]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.021
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.012
% 3.04/0.99  total_time:                             0.196
% 3.04/0.99  num_of_symbols:                         59
% 3.04/0.99  num_of_terms:                           5834
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          0
% 3.04/0.99  num_of_split_atoms:                     0
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    55
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        2
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       137
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        37
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        3
% 3.04/0.99  pred_elim:                              4
% 3.04/0.99  pred_elim_cl:                           6
% 3.04/0.99  pred_elim_cycles:                       6
% 3.04/0.99  merged_defs:                            0
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          0
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.004
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                25
% 3.04/0.99  conjectures:                            7
% 3.04/0.99  epr:                                    3
% 3.04/0.99  horn:                                   22
% 3.04/0.99  ground:                                 13
% 3.04/0.99  unary:                                  9
% 3.04/0.99  binary:                                 6
% 3.04/0.99  lits:                                   56
% 3.04/0.99  lits_eq:                                25
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                0
% 3.04/0.99  fd_pseudo_cond:                         0
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      29
% 3.04/0.99  prop_fast_solver_calls:                 863
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    2239
% 3.04/0.99  prop_preprocess_simplified:             6412
% 3.04/0.99  prop_fo_subsumed:                       19
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    730
% 3.04/0.99  inst_num_in_passive:                    345
% 3.04/0.99  inst_num_in_active:                     366
% 3.04/0.99  inst_num_in_unprocessed:                19
% 3.04/0.99  inst_num_of_loops:                      400
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          32
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                1
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      71
% 3.04/0.99  inst_num_of_non_proper_insts:           307
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       141
% 3.04/0.99  res_forward_subset_subsumed:            17
% 3.04/0.99  res_backward_subset_subsumed:           0
% 3.04/0.99  res_forward_subsumed:                   0
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     0
% 3.04/0.99  res_backward_subsumption_resolution:    0
% 3.04/0.99  res_clause_to_clause_subsumption:       215
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      23
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     121
% 3.04/0.99  sup_num_in_active:                      74
% 3.04/0.99  sup_num_in_passive:                     47
% 3.04/0.99  sup_num_of_loops:                       79
% 3.04/0.99  sup_fw_superposition:                   68
% 3.04/0.99  sup_bw_superposition:                   33
% 3.04/0.99  sup_immediate_simplified:               12
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    3
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 0
% 3.04/0.99  sim_bw_subset_subsumed:                 0
% 3.04/0.99  sim_fw_subsumed:                        0
% 3.04/0.99  sim_bw_subsumed:                        0
% 3.04/0.99  sim_fw_subsumption_res:                 1
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      0
% 3.04/0.99  sim_eq_tautology_del:                   1
% 3.04/0.99  sim_eq_res_simp:                        0
% 3.04/0.99  sim_fw_demodulated:                     0
% 3.04/0.99  sim_bw_demodulated:                     6
% 3.04/0.99  sim_light_normalised:                   12
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
