%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:40 EST 2020

% Result     : Theorem 11.11s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 902 expanded)
%              Number of clauses        :   93 ( 284 expanded)
%              Number of leaves         :   16 ( 218 expanded)
%              Depth                    :   21
%              Number of atoms          :  484 (6152 expanded)
%              Number of equality atoms :  220 (2092 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1009,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1011,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1015,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2408,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1015])).

cnf(c_4290,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_2408])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4457,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4290,c_35])).

cnf(c_4458,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4457])).

cnf(c_4465,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_4458])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1012,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2398,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1012])).

cnf(c_2516,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_35])).

cnf(c_2517,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2516])).

cnf(c_2524,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_2517])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2595,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_32])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2597,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2595,c_25])).

cnf(c_4469,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4465,c_2595,c_2597])).

cnf(c_4564,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4469,c_32])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1018,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4569,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4564,c_1018])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1133,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_4915,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4569,c_34,c_37,c_1133,c_1320])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_9])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_2333,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1006])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1022,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2469,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_1022])).

cnf(c_4920,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_4915,c_2469])).

cnf(c_1017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1352,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1017])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1019,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1408,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1352,c_1019])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1016,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1773,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1011,c_1016])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_445,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_447,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_26,c_23])).

cnf(c_1775,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1773,c_447])).

cnf(c_2208,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1408,c_1408,c_1775])).

cnf(c_32643,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4920,c_2208])).

cnf(c_2334,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1006])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_28])).

cnf(c_1007,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_330,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1682,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_37,c_330,c_1133])).

cnf(c_1683,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1682])).

cnf(c_1963,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1775,c_1683])).

cnf(c_2473,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2334,c_1963])).

cnf(c_1353,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1017])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1020,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1828,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1020])).

cnf(c_2833,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1353,c_1828])).

cnf(c_3029,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2473,c_2473,c_2833])).

cnf(c_4567,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4564,c_3029])).

cnf(c_33253,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_32643,c_4567])).

cnf(c_1406,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1009,c_1015])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1544,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1406,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33253,c_1544])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:59:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.11/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/1.99  
% 11.11/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.11/1.99  
% 11.11/1.99  ------  iProver source info
% 11.11/1.99  
% 11.11/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.11/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.11/1.99  git: non_committed_changes: false
% 11.11/1.99  git: last_make_outside_of_git: false
% 11.11/1.99  
% 11.11/1.99  ------ 
% 11.11/1.99  
% 11.11/1.99  ------ Input Options
% 11.11/1.99  
% 11.11/1.99  --out_options                           all
% 11.11/1.99  --tptp_safe_out                         true
% 11.11/1.99  --problem_path                          ""
% 11.11/1.99  --include_path                          ""
% 11.11/1.99  --clausifier                            res/vclausify_rel
% 11.11/1.99  --clausifier_options                    ""
% 11.11/1.99  --stdin                                 false
% 11.11/1.99  --stats_out                             all
% 11.11/1.99  
% 11.11/1.99  ------ General Options
% 11.11/1.99  
% 11.11/1.99  --fof                                   false
% 11.11/1.99  --time_out_real                         305.
% 11.11/1.99  --time_out_virtual                      -1.
% 11.11/1.99  --symbol_type_check                     false
% 11.11/1.99  --clausify_out                          false
% 11.11/1.99  --sig_cnt_out                           false
% 11.11/1.99  --trig_cnt_out                          false
% 11.11/1.99  --trig_cnt_out_tolerance                1.
% 11.11/1.99  --trig_cnt_out_sk_spl                   false
% 11.11/1.99  --abstr_cl_out                          false
% 11.11/1.99  
% 11.11/1.99  ------ Global Options
% 11.11/1.99  
% 11.11/1.99  --schedule                              default
% 11.11/1.99  --add_important_lit                     false
% 11.11/1.99  --prop_solver_per_cl                    1000
% 11.11/1.99  --min_unsat_core                        false
% 11.11/1.99  --soft_assumptions                      false
% 11.11/1.99  --soft_lemma_size                       3
% 11.11/1.99  --prop_impl_unit_size                   0
% 11.11/1.99  --prop_impl_unit                        []
% 11.11/1.99  --share_sel_clauses                     true
% 11.11/1.99  --reset_solvers                         false
% 11.11/1.99  --bc_imp_inh                            [conj_cone]
% 11.11/1.99  --conj_cone_tolerance                   3.
% 11.11/1.99  --extra_neg_conj                        none
% 11.11/1.99  --large_theory_mode                     true
% 11.11/1.99  --prolific_symb_bound                   200
% 11.11/1.99  --lt_threshold                          2000
% 11.11/1.99  --clause_weak_htbl                      true
% 11.11/1.99  --gc_record_bc_elim                     false
% 11.11/1.99  
% 11.11/1.99  ------ Preprocessing Options
% 11.11/1.99  
% 11.11/1.99  --preprocessing_flag                    true
% 11.11/1.99  --time_out_prep_mult                    0.1
% 11.11/1.99  --splitting_mode                        input
% 11.11/1.99  --splitting_grd                         true
% 11.11/1.99  --splitting_cvd                         false
% 11.11/1.99  --splitting_cvd_svl                     false
% 11.11/1.99  --splitting_nvd                         32
% 11.11/1.99  --sub_typing                            true
% 11.11/1.99  --prep_gs_sim                           true
% 11.11/1.99  --prep_unflatten                        true
% 11.11/1.99  --prep_res_sim                          true
% 11.11/1.99  --prep_upred                            true
% 11.11/1.99  --prep_sem_filter                       exhaustive
% 11.11/1.99  --prep_sem_filter_out                   false
% 11.11/1.99  --pred_elim                             true
% 11.11/1.99  --res_sim_input                         true
% 11.11/1.99  --eq_ax_congr_red                       true
% 11.11/1.99  --pure_diseq_elim                       true
% 11.11/1.99  --brand_transform                       false
% 11.11/1.99  --non_eq_to_eq                          false
% 11.11/1.99  --prep_def_merge                        true
% 11.11/1.99  --prep_def_merge_prop_impl              false
% 11.11/1.99  --prep_def_merge_mbd                    true
% 11.11/1.99  --prep_def_merge_tr_red                 false
% 11.11/1.99  --prep_def_merge_tr_cl                  false
% 11.11/1.99  --smt_preprocessing                     true
% 11.11/1.99  --smt_ac_axioms                         fast
% 11.11/1.99  --preprocessed_out                      false
% 11.11/1.99  --preprocessed_stats                    false
% 11.11/1.99  
% 11.11/1.99  ------ Abstraction refinement Options
% 11.11/1.99  
% 11.11/1.99  --abstr_ref                             []
% 11.11/1.99  --abstr_ref_prep                        false
% 11.11/1.99  --abstr_ref_until_sat                   false
% 11.11/1.99  --abstr_ref_sig_restrict                funpre
% 11.11/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.11/1.99  --abstr_ref_under                       []
% 11.11/1.99  
% 11.11/1.99  ------ SAT Options
% 11.11/1.99  
% 11.11/1.99  --sat_mode                              false
% 11.11/1.99  --sat_fm_restart_options                ""
% 11.11/1.99  --sat_gr_def                            false
% 11.11/1.99  --sat_epr_types                         true
% 11.11/1.99  --sat_non_cyclic_types                  false
% 11.11/1.99  --sat_finite_models                     false
% 11.11/1.99  --sat_fm_lemmas                         false
% 11.11/1.99  --sat_fm_prep                           false
% 11.11/1.99  --sat_fm_uc_incr                        true
% 11.11/1.99  --sat_out_model                         small
% 11.11/1.99  --sat_out_clauses                       false
% 11.11/1.99  
% 11.11/1.99  ------ QBF Options
% 11.11/1.99  
% 11.11/1.99  --qbf_mode                              false
% 11.11/1.99  --qbf_elim_univ                         false
% 11.11/1.99  --qbf_dom_inst                          none
% 11.11/1.99  --qbf_dom_pre_inst                      false
% 11.11/1.99  --qbf_sk_in                             false
% 11.11/1.99  --qbf_pred_elim                         true
% 11.11/1.99  --qbf_split                             512
% 11.11/1.99  
% 11.11/1.99  ------ BMC1 Options
% 11.11/1.99  
% 11.11/1.99  --bmc1_incremental                      false
% 11.11/1.99  --bmc1_axioms                           reachable_all
% 11.11/1.99  --bmc1_min_bound                        0
% 11.11/1.99  --bmc1_max_bound                        -1
% 11.11/1.99  --bmc1_max_bound_default                -1
% 11.11/1.99  --bmc1_symbol_reachability              true
% 11.11/1.99  --bmc1_property_lemmas                  false
% 11.11/1.99  --bmc1_k_induction                      false
% 11.11/1.99  --bmc1_non_equiv_states                 false
% 11.11/1.99  --bmc1_deadlock                         false
% 11.11/1.99  --bmc1_ucm                              false
% 11.11/1.99  --bmc1_add_unsat_core                   none
% 11.11/1.99  --bmc1_unsat_core_children              false
% 11.11/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.11/1.99  --bmc1_out_stat                         full
% 11.11/1.99  --bmc1_ground_init                      false
% 11.11/1.99  --bmc1_pre_inst_next_state              false
% 11.11/1.99  --bmc1_pre_inst_state                   false
% 11.11/1.99  --bmc1_pre_inst_reach_state             false
% 11.11/1.99  --bmc1_out_unsat_core                   false
% 11.11/1.99  --bmc1_aig_witness_out                  false
% 11.11/1.99  --bmc1_verbose                          false
% 11.11/1.99  --bmc1_dump_clauses_tptp                false
% 11.11/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.11/1.99  --bmc1_dump_file                        -
% 11.11/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.11/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.11/1.99  --bmc1_ucm_extend_mode                  1
% 11.11/1.99  --bmc1_ucm_init_mode                    2
% 11.11/1.99  --bmc1_ucm_cone_mode                    none
% 11.11/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.11/1.99  --bmc1_ucm_relax_model                  4
% 11.11/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.11/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.11/1.99  --bmc1_ucm_layered_model                none
% 11.11/1.99  --bmc1_ucm_max_lemma_size               10
% 11.11/1.99  
% 11.11/1.99  ------ AIG Options
% 11.11/1.99  
% 11.11/1.99  --aig_mode                              false
% 11.11/1.99  
% 11.11/1.99  ------ Instantiation Options
% 11.11/1.99  
% 11.11/1.99  --instantiation_flag                    true
% 11.11/1.99  --inst_sos_flag                         true
% 11.11/1.99  --inst_sos_phase                        true
% 11.11/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.11/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.11/1.99  --inst_lit_sel_side                     num_symb
% 11.11/1.99  --inst_solver_per_active                1400
% 11.11/1.99  --inst_solver_calls_frac                1.
% 11.11/1.99  --inst_passive_queue_type               priority_queues
% 11.11/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.11/1.99  --inst_passive_queues_freq              [25;2]
% 11.11/1.99  --inst_dismatching                      true
% 11.11/1.99  --inst_eager_unprocessed_to_passive     true
% 11.11/1.99  --inst_prop_sim_given                   true
% 11.11/1.99  --inst_prop_sim_new                     false
% 11.11/1.99  --inst_subs_new                         false
% 11.11/1.99  --inst_eq_res_simp                      false
% 11.11/1.99  --inst_subs_given                       false
% 11.11/1.99  --inst_orphan_elimination               true
% 11.11/1.99  --inst_learning_loop_flag               true
% 11.11/1.99  --inst_learning_start                   3000
% 11.11/1.99  --inst_learning_factor                  2
% 11.11/1.99  --inst_start_prop_sim_after_learn       3
% 11.11/1.99  --inst_sel_renew                        solver
% 11.11/1.99  --inst_lit_activity_flag                true
% 11.11/1.99  --inst_restr_to_given                   false
% 11.11/1.99  --inst_activity_threshold               500
% 11.11/1.99  --inst_out_proof                        true
% 11.11/1.99  
% 11.11/1.99  ------ Resolution Options
% 11.11/1.99  
% 11.11/1.99  --resolution_flag                       true
% 11.11/1.99  --res_lit_sel                           adaptive
% 11.11/1.99  --res_lit_sel_side                      none
% 11.11/1.99  --res_ordering                          kbo
% 11.11/1.99  --res_to_prop_solver                    active
% 11.11/1.99  --res_prop_simpl_new                    false
% 11.11/1.99  --res_prop_simpl_given                  true
% 11.11/1.99  --res_passive_queue_type                priority_queues
% 11.11/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.11/1.99  --res_passive_queues_freq               [15;5]
% 11.11/1.99  --res_forward_subs                      full
% 11.11/1.99  --res_backward_subs                     full
% 11.11/1.99  --res_forward_subs_resolution           true
% 11.11/1.99  --res_backward_subs_resolution          true
% 11.11/1.99  --res_orphan_elimination                true
% 11.11/1.99  --res_time_limit                        2.
% 11.11/1.99  --res_out_proof                         true
% 11.11/1.99  
% 11.11/1.99  ------ Superposition Options
% 11.11/1.99  
% 11.11/1.99  --superposition_flag                    true
% 11.11/1.99  --sup_passive_queue_type                priority_queues
% 11.11/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.11/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.11/1.99  --demod_completeness_check              fast
% 11.11/1.99  --demod_use_ground                      true
% 11.11/1.99  --sup_to_prop_solver                    passive
% 11.11/1.99  --sup_prop_simpl_new                    true
% 11.11/1.99  --sup_prop_simpl_given                  true
% 11.11/1.99  --sup_fun_splitting                     true
% 11.11/1.99  --sup_smt_interval                      50000
% 11.11/1.99  
% 11.11/1.99  ------ Superposition Simplification Setup
% 11.11/1.99  
% 11.11/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.11/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.11/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.11/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.11/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.11/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.11/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.11/1.99  --sup_immed_triv                        [TrivRules]
% 11.11/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_immed_bw_main                     []
% 11.11/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.11/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.11/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_input_bw                          []
% 11.11/1.99  
% 11.11/1.99  ------ Combination Options
% 11.11/1.99  
% 11.11/1.99  --comb_res_mult                         3
% 11.11/1.99  --comb_sup_mult                         2
% 11.11/1.99  --comb_inst_mult                        10
% 11.11/1.99  
% 11.11/1.99  ------ Debug Options
% 11.11/1.99  
% 11.11/1.99  --dbg_backtrace                         false
% 11.11/1.99  --dbg_dump_prop_clauses                 false
% 11.11/1.99  --dbg_dump_prop_clauses_file            -
% 11.11/1.99  --dbg_out_stat                          false
% 11.11/1.99  ------ Parsing...
% 11.11/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.11/1.99  
% 11.11/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.11/1.99  
% 11.11/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.11/1.99  
% 11.11/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.11/1.99  ------ Proving...
% 11.11/1.99  ------ Problem Properties 
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  clauses                                 26
% 11.11/1.99  conjectures                             7
% 11.11/1.99  EPR                                     5
% 11.11/1.99  Horn                                    23
% 11.11/1.99  unary                                   9
% 11.11/1.99  binary                                  6
% 11.11/1.99  lits                                    62
% 11.11/1.99  lits eq                                 23
% 11.11/1.99  fd_pure                                 0
% 11.11/1.99  fd_pseudo                               0
% 11.11/1.99  fd_cond                                 0
% 11.11/1.99  fd_pseudo_cond                          1
% 11.11/1.99  AC symbols                              0
% 11.11/1.99  
% 11.11/1.99  ------ Schedule dynamic 5 is on 
% 11.11/1.99  
% 11.11/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  ------ 
% 11.11/1.99  Current options:
% 11.11/1.99  ------ 
% 11.11/1.99  
% 11.11/1.99  ------ Input Options
% 11.11/1.99  
% 11.11/1.99  --out_options                           all
% 11.11/1.99  --tptp_safe_out                         true
% 11.11/1.99  --problem_path                          ""
% 11.11/1.99  --include_path                          ""
% 11.11/1.99  --clausifier                            res/vclausify_rel
% 11.11/1.99  --clausifier_options                    ""
% 11.11/1.99  --stdin                                 false
% 11.11/1.99  --stats_out                             all
% 11.11/1.99  
% 11.11/1.99  ------ General Options
% 11.11/1.99  
% 11.11/1.99  --fof                                   false
% 11.11/1.99  --time_out_real                         305.
% 11.11/1.99  --time_out_virtual                      -1.
% 11.11/1.99  --symbol_type_check                     false
% 11.11/1.99  --clausify_out                          false
% 11.11/1.99  --sig_cnt_out                           false
% 11.11/1.99  --trig_cnt_out                          false
% 11.11/1.99  --trig_cnt_out_tolerance                1.
% 11.11/1.99  --trig_cnt_out_sk_spl                   false
% 11.11/1.99  --abstr_cl_out                          false
% 11.11/1.99  
% 11.11/1.99  ------ Global Options
% 11.11/1.99  
% 11.11/1.99  --schedule                              default
% 11.11/1.99  --add_important_lit                     false
% 11.11/1.99  --prop_solver_per_cl                    1000
% 11.11/1.99  --min_unsat_core                        false
% 11.11/1.99  --soft_assumptions                      false
% 11.11/1.99  --soft_lemma_size                       3
% 11.11/1.99  --prop_impl_unit_size                   0
% 11.11/1.99  --prop_impl_unit                        []
% 11.11/1.99  --share_sel_clauses                     true
% 11.11/1.99  --reset_solvers                         false
% 11.11/1.99  --bc_imp_inh                            [conj_cone]
% 11.11/1.99  --conj_cone_tolerance                   3.
% 11.11/1.99  --extra_neg_conj                        none
% 11.11/1.99  --large_theory_mode                     true
% 11.11/1.99  --prolific_symb_bound                   200
% 11.11/1.99  --lt_threshold                          2000
% 11.11/1.99  --clause_weak_htbl                      true
% 11.11/1.99  --gc_record_bc_elim                     false
% 11.11/1.99  
% 11.11/1.99  ------ Preprocessing Options
% 11.11/1.99  
% 11.11/1.99  --preprocessing_flag                    true
% 11.11/1.99  --time_out_prep_mult                    0.1
% 11.11/1.99  --splitting_mode                        input
% 11.11/1.99  --splitting_grd                         true
% 11.11/1.99  --splitting_cvd                         false
% 11.11/1.99  --splitting_cvd_svl                     false
% 11.11/1.99  --splitting_nvd                         32
% 11.11/1.99  --sub_typing                            true
% 11.11/1.99  --prep_gs_sim                           true
% 11.11/1.99  --prep_unflatten                        true
% 11.11/1.99  --prep_res_sim                          true
% 11.11/1.99  --prep_upred                            true
% 11.11/1.99  --prep_sem_filter                       exhaustive
% 11.11/1.99  --prep_sem_filter_out                   false
% 11.11/1.99  --pred_elim                             true
% 11.11/1.99  --res_sim_input                         true
% 11.11/1.99  --eq_ax_congr_red                       true
% 11.11/1.99  --pure_diseq_elim                       true
% 11.11/1.99  --brand_transform                       false
% 11.11/1.99  --non_eq_to_eq                          false
% 11.11/1.99  --prep_def_merge                        true
% 11.11/1.99  --prep_def_merge_prop_impl              false
% 11.11/1.99  --prep_def_merge_mbd                    true
% 11.11/1.99  --prep_def_merge_tr_red                 false
% 11.11/1.99  --prep_def_merge_tr_cl                  false
% 11.11/1.99  --smt_preprocessing                     true
% 11.11/1.99  --smt_ac_axioms                         fast
% 11.11/1.99  --preprocessed_out                      false
% 11.11/1.99  --preprocessed_stats                    false
% 11.11/1.99  
% 11.11/1.99  ------ Abstraction refinement Options
% 11.11/1.99  
% 11.11/1.99  --abstr_ref                             []
% 11.11/1.99  --abstr_ref_prep                        false
% 11.11/1.99  --abstr_ref_until_sat                   false
% 11.11/1.99  --abstr_ref_sig_restrict                funpre
% 11.11/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.11/1.99  --abstr_ref_under                       []
% 11.11/1.99  
% 11.11/1.99  ------ SAT Options
% 11.11/1.99  
% 11.11/1.99  --sat_mode                              false
% 11.11/1.99  --sat_fm_restart_options                ""
% 11.11/1.99  --sat_gr_def                            false
% 11.11/1.99  --sat_epr_types                         true
% 11.11/1.99  --sat_non_cyclic_types                  false
% 11.11/1.99  --sat_finite_models                     false
% 11.11/1.99  --sat_fm_lemmas                         false
% 11.11/1.99  --sat_fm_prep                           false
% 11.11/1.99  --sat_fm_uc_incr                        true
% 11.11/1.99  --sat_out_model                         small
% 11.11/1.99  --sat_out_clauses                       false
% 11.11/1.99  
% 11.11/1.99  ------ QBF Options
% 11.11/1.99  
% 11.11/1.99  --qbf_mode                              false
% 11.11/1.99  --qbf_elim_univ                         false
% 11.11/1.99  --qbf_dom_inst                          none
% 11.11/1.99  --qbf_dom_pre_inst                      false
% 11.11/1.99  --qbf_sk_in                             false
% 11.11/1.99  --qbf_pred_elim                         true
% 11.11/1.99  --qbf_split                             512
% 11.11/1.99  
% 11.11/1.99  ------ BMC1 Options
% 11.11/1.99  
% 11.11/1.99  --bmc1_incremental                      false
% 11.11/1.99  --bmc1_axioms                           reachable_all
% 11.11/1.99  --bmc1_min_bound                        0
% 11.11/1.99  --bmc1_max_bound                        -1
% 11.11/1.99  --bmc1_max_bound_default                -1
% 11.11/1.99  --bmc1_symbol_reachability              true
% 11.11/1.99  --bmc1_property_lemmas                  false
% 11.11/1.99  --bmc1_k_induction                      false
% 11.11/1.99  --bmc1_non_equiv_states                 false
% 11.11/1.99  --bmc1_deadlock                         false
% 11.11/1.99  --bmc1_ucm                              false
% 11.11/1.99  --bmc1_add_unsat_core                   none
% 11.11/1.99  --bmc1_unsat_core_children              false
% 11.11/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.11/1.99  --bmc1_out_stat                         full
% 11.11/1.99  --bmc1_ground_init                      false
% 11.11/1.99  --bmc1_pre_inst_next_state              false
% 11.11/1.99  --bmc1_pre_inst_state                   false
% 11.11/1.99  --bmc1_pre_inst_reach_state             false
% 11.11/1.99  --bmc1_out_unsat_core                   false
% 11.11/1.99  --bmc1_aig_witness_out                  false
% 11.11/1.99  --bmc1_verbose                          false
% 11.11/1.99  --bmc1_dump_clauses_tptp                false
% 11.11/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.11/1.99  --bmc1_dump_file                        -
% 11.11/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.11/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.11/1.99  --bmc1_ucm_extend_mode                  1
% 11.11/1.99  --bmc1_ucm_init_mode                    2
% 11.11/1.99  --bmc1_ucm_cone_mode                    none
% 11.11/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.11/1.99  --bmc1_ucm_relax_model                  4
% 11.11/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.11/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.11/1.99  --bmc1_ucm_layered_model                none
% 11.11/1.99  --bmc1_ucm_max_lemma_size               10
% 11.11/1.99  
% 11.11/1.99  ------ AIG Options
% 11.11/1.99  
% 11.11/1.99  --aig_mode                              false
% 11.11/1.99  
% 11.11/1.99  ------ Instantiation Options
% 11.11/1.99  
% 11.11/1.99  --instantiation_flag                    true
% 11.11/1.99  --inst_sos_flag                         true
% 11.11/1.99  --inst_sos_phase                        true
% 11.11/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.11/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.11/1.99  --inst_lit_sel_side                     none
% 11.11/1.99  --inst_solver_per_active                1400
% 11.11/1.99  --inst_solver_calls_frac                1.
% 11.11/1.99  --inst_passive_queue_type               priority_queues
% 11.11/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.11/1.99  --inst_passive_queues_freq              [25;2]
% 11.11/1.99  --inst_dismatching                      true
% 11.11/1.99  --inst_eager_unprocessed_to_passive     true
% 11.11/1.99  --inst_prop_sim_given                   true
% 11.11/1.99  --inst_prop_sim_new                     false
% 11.11/1.99  --inst_subs_new                         false
% 11.11/1.99  --inst_eq_res_simp                      false
% 11.11/1.99  --inst_subs_given                       false
% 11.11/1.99  --inst_orphan_elimination               true
% 11.11/1.99  --inst_learning_loop_flag               true
% 11.11/1.99  --inst_learning_start                   3000
% 11.11/1.99  --inst_learning_factor                  2
% 11.11/1.99  --inst_start_prop_sim_after_learn       3
% 11.11/1.99  --inst_sel_renew                        solver
% 11.11/1.99  --inst_lit_activity_flag                true
% 11.11/1.99  --inst_restr_to_given                   false
% 11.11/1.99  --inst_activity_threshold               500
% 11.11/1.99  --inst_out_proof                        true
% 11.11/1.99  
% 11.11/1.99  ------ Resolution Options
% 11.11/1.99  
% 11.11/1.99  --resolution_flag                       false
% 11.11/1.99  --res_lit_sel                           adaptive
% 11.11/1.99  --res_lit_sel_side                      none
% 11.11/1.99  --res_ordering                          kbo
% 11.11/1.99  --res_to_prop_solver                    active
% 11.11/1.99  --res_prop_simpl_new                    false
% 11.11/1.99  --res_prop_simpl_given                  true
% 11.11/1.99  --res_passive_queue_type                priority_queues
% 11.11/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.11/1.99  --res_passive_queues_freq               [15;5]
% 11.11/1.99  --res_forward_subs                      full
% 11.11/1.99  --res_backward_subs                     full
% 11.11/1.99  --res_forward_subs_resolution           true
% 11.11/1.99  --res_backward_subs_resolution          true
% 11.11/1.99  --res_orphan_elimination                true
% 11.11/1.99  --res_time_limit                        2.
% 11.11/1.99  --res_out_proof                         true
% 11.11/1.99  
% 11.11/1.99  ------ Superposition Options
% 11.11/1.99  
% 11.11/1.99  --superposition_flag                    true
% 11.11/1.99  --sup_passive_queue_type                priority_queues
% 11.11/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.11/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.11/1.99  --demod_completeness_check              fast
% 11.11/1.99  --demod_use_ground                      true
% 11.11/1.99  --sup_to_prop_solver                    passive
% 11.11/1.99  --sup_prop_simpl_new                    true
% 11.11/1.99  --sup_prop_simpl_given                  true
% 11.11/1.99  --sup_fun_splitting                     true
% 11.11/1.99  --sup_smt_interval                      50000
% 11.11/1.99  
% 11.11/1.99  ------ Superposition Simplification Setup
% 11.11/1.99  
% 11.11/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.11/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.11/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.11/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.11/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.11/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.11/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.11/1.99  --sup_immed_triv                        [TrivRules]
% 11.11/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_immed_bw_main                     []
% 11.11/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.11/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.11/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.11/1.99  --sup_input_bw                          []
% 11.11/1.99  
% 11.11/1.99  ------ Combination Options
% 11.11/1.99  
% 11.11/1.99  --comb_res_mult                         3
% 11.11/1.99  --comb_sup_mult                         2
% 11.11/1.99  --comb_inst_mult                        10
% 11.11/1.99  
% 11.11/1.99  ------ Debug Options
% 11.11/1.99  
% 11.11/1.99  --dbg_backtrace                         false
% 11.11/1.99  --dbg_dump_prop_clauses                 false
% 11.11/1.99  --dbg_dump_prop_clauses_file            -
% 11.11/1.99  --dbg_out_stat                          false
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  ------ Proving...
% 11.11/1.99  
% 11.11/1.99  
% 11.11/1.99  % SZS status Theorem for theBenchmark.p
% 11.11/1.99  
% 11.11/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.11/1.99  
% 11.11/1.99  fof(f14,conjecture,(
% 11.11/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f15,negated_conjecture,(
% 11.11/1.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.11/1.99    inference(negated_conjecture,[],[f14])).
% 11.11/1.99  
% 11.11/1.99  fof(f33,plain,(
% 11.11/1.99    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.11/1.99    inference(ennf_transformation,[],[f15])).
% 11.11/1.99  
% 11.11/1.99  fof(f34,plain,(
% 11.11/1.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.11/1.99    inference(flattening,[],[f33])).
% 11.11/1.99  
% 11.11/1.99  fof(f40,plain,(
% 11.11/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 11.11/1.99    introduced(choice_axiom,[])).
% 11.11/1.99  
% 11.11/1.99  fof(f39,plain,(
% 11.11/1.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.11/1.99    introduced(choice_axiom,[])).
% 11.11/1.99  
% 11.11/1.99  fof(f41,plain,(
% 11.11/1.99    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.11/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39])).
% 11.11/1.99  
% 11.11/1.99  fof(f66,plain,(
% 11.11/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f69,plain,(
% 11.11/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f12,axiom,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f29,plain,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.11/1.99    inference(ennf_transformation,[],[f12])).
% 11.11/1.99  
% 11.11/1.99  fof(f30,plain,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.11/1.99    inference(flattening,[],[f29])).
% 11.11/1.99  
% 11.11/1.99  fof(f62,plain,(
% 11.11/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f30])).
% 11.11/1.99  
% 11.11/1.99  fof(f10,axiom,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f26,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(ennf_transformation,[],[f10])).
% 11.11/1.99  
% 11.11/1.99  fof(f54,plain,(
% 11.11/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.11/1.99    inference(cnf_transformation,[],[f26])).
% 11.11/1.99  
% 11.11/1.99  fof(f67,plain,(
% 11.11/1.99    v1_funct_1(sK4)),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f13,axiom,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f31,plain,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.11/1.99    inference(ennf_transformation,[],[f13])).
% 11.11/1.99  
% 11.11/1.99  fof(f32,plain,(
% 11.11/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.11/1.99    inference(flattening,[],[f31])).
% 11.11/1.99  
% 11.11/1.99  fof(f63,plain,(
% 11.11/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f32])).
% 11.11/1.99  
% 11.11/1.99  fof(f64,plain,(
% 11.11/1.99    v1_funct_1(sK3)),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f70,plain,(
% 11.11/1.99    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f5,axiom,(
% 11.11/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f20,plain,(
% 11.11/1.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.11/1.99    inference(ennf_transformation,[],[f5])).
% 11.11/1.99  
% 11.11/1.99  fof(f49,plain,(
% 11.11/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f20])).
% 11.11/1.99  
% 11.11/1.99  fof(f7,axiom,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f23,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(ennf_transformation,[],[f7])).
% 11.11/1.99  
% 11.11/1.99  fof(f51,plain,(
% 11.11/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.11/1.99    inference(cnf_transformation,[],[f23])).
% 11.11/1.99  
% 11.11/1.99  fof(f2,axiom,(
% 11.11/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f17,plain,(
% 11.11/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.11/1.99    inference(ennf_transformation,[],[f2])).
% 11.11/1.99  
% 11.11/1.99  fof(f37,plain,(
% 11.11/1.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.11/1.99    inference(nnf_transformation,[],[f17])).
% 11.11/1.99  
% 11.11/1.99  fof(f45,plain,(
% 11.11/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f37])).
% 11.11/1.99  
% 11.11/1.99  fof(f8,axiom,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f16,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.11/1.99    inference(pure_predicate_removal,[],[f8])).
% 11.11/1.99  
% 11.11/1.99  fof(f24,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(ennf_transformation,[],[f16])).
% 11.11/1.99  
% 11.11/1.99  fof(f52,plain,(
% 11.11/1.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.11/1.99    inference(cnf_transformation,[],[f24])).
% 11.11/1.99  
% 11.11/1.99  fof(f1,axiom,(
% 11.11/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f35,plain,(
% 11.11/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.11/1.99    inference(nnf_transformation,[],[f1])).
% 11.11/1.99  
% 11.11/1.99  fof(f36,plain,(
% 11.11/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.11/1.99    inference(flattening,[],[f35])).
% 11.11/1.99  
% 11.11/1.99  fof(f44,plain,(
% 11.11/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f36])).
% 11.11/1.99  
% 11.11/1.99  fof(f4,axiom,(
% 11.11/1.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f19,plain,(
% 11.11/1.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 11.11/1.99    inference(ennf_transformation,[],[f4])).
% 11.11/1.99  
% 11.11/1.99  fof(f48,plain,(
% 11.11/1.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f19])).
% 11.11/1.99  
% 11.11/1.99  fof(f9,axiom,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f25,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(ennf_transformation,[],[f9])).
% 11.11/1.99  
% 11.11/1.99  fof(f53,plain,(
% 11.11/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.11/1.99    inference(cnf_transformation,[],[f25])).
% 11.11/1.99  
% 11.11/1.99  fof(f11,axiom,(
% 11.11/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f27,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(ennf_transformation,[],[f11])).
% 11.11/1.99  
% 11.11/1.99  fof(f28,plain,(
% 11.11/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(flattening,[],[f27])).
% 11.11/1.99  
% 11.11/1.99  fof(f38,plain,(
% 11.11/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.11/1.99    inference(nnf_transformation,[],[f28])).
% 11.11/1.99  
% 11.11/1.99  fof(f55,plain,(
% 11.11/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.11/1.99    inference(cnf_transformation,[],[f38])).
% 11.11/1.99  
% 11.11/1.99  fof(f68,plain,(
% 11.11/1.99    v1_funct_2(sK4,sK1,sK2)),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f72,plain,(
% 11.11/1.99    k1_xboole_0 != sK2),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f6,axiom,(
% 11.11/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f21,plain,(
% 11.11/1.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.11/1.99    inference(ennf_transformation,[],[f6])).
% 11.11/1.99  
% 11.11/1.99  fof(f22,plain,(
% 11.11/1.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.11/1.99    inference(flattening,[],[f21])).
% 11.11/1.99  
% 11.11/1.99  fof(f50,plain,(
% 11.11/1.99    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f22])).
% 11.11/1.99  
% 11.11/1.99  fof(f71,plain,(
% 11.11/1.99    v2_funct_1(sK4)),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  fof(f3,axiom,(
% 11.11/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 11.11/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.11/1.99  
% 11.11/1.99  fof(f18,plain,(
% 11.11/1.99    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.11/1.99    inference(ennf_transformation,[],[f3])).
% 11.11/1.99  
% 11.11/1.99  fof(f47,plain,(
% 11.11/1.99    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.11/1.99    inference(cnf_transformation,[],[f18])).
% 11.11/1.99  
% 11.11/1.99  fof(f73,plain,(
% 11.11/1.99    k2_relset_1(sK0,sK1,sK3) != sK1),
% 11.11/1.99    inference(cnf_transformation,[],[f41])).
% 11.11/1.99  
% 11.11/1.99  cnf(c_29,negated_conjecture,
% 11.11/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.11/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1009,plain,
% 11.11/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_26,negated_conjecture,
% 11.11/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.11/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1011,plain,
% 11.11/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_19,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.11/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.11/1.99      | ~ v1_funct_1(X0)
% 11.11/1.99      | ~ v1_funct_1(X3) ),
% 11.11/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1014,plain,
% 11.11/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.11/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.11/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.11/1.99      | v1_funct_1(X0) != iProver_top
% 11.11/1.99      | v1_funct_1(X3) != iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_12,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.11/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1015,plain,
% 11.11/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2408,plain,
% 11.11/1.99      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 11.11/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 11.11/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 11.11/1.99      | v1_funct_1(X5) != iProver_top
% 11.11/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1014,c_1015]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4290,plain,
% 11.11/1.99      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | v1_funct_1(X2) != iProver_top
% 11.11/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1011,c_2408]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_28,negated_conjecture,
% 11.11/1.99      ( v1_funct_1(sK4) ),
% 11.11/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_35,plain,
% 11.11/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4457,plain,
% 11.11/1.99      ( v1_funct_1(X2) != iProver_top
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_4290,c_35]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4458,plain,
% 11.11/1.99      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.11/1.99      inference(renaming,[status(thm)],[c_4457]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4465,plain,
% 11.11/1.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 11.11/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1009,c_4458]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_21,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.11/1.99      | ~ v1_funct_1(X0)
% 11.11/1.99      | ~ v1_funct_1(X3)
% 11.11/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.11/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1012,plain,
% 11.11/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.11/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.11/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | v1_funct_1(X5) != iProver_top
% 11.11/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2398,plain,
% 11.11/1.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | v1_funct_1(X2) != iProver_top
% 11.11/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1011,c_1012]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2516,plain,
% 11.11/1.99      ( v1_funct_1(X2) != iProver_top
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_2398,c_35]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2517,plain,
% 11.11/1.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.11/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.11/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.11/1.99      inference(renaming,[status(thm)],[c_2516]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2524,plain,
% 11.11/1.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.11/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1009,c_2517]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_31,negated_conjecture,
% 11.11/1.99      ( v1_funct_1(sK3) ),
% 11.11/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_32,plain,
% 11.11/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2595,plain,
% 11.11/1.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_2524,c_32]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_25,negated_conjecture,
% 11.11/1.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 11.11/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2597,plain,
% 11.11/1.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 11.11/1.99      inference(demodulation,[status(thm)],[c_2595,c_25]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4469,plain,
% 11.11/1.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 11.11/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.11/1.99      inference(light_normalisation,[status(thm)],[c_4465,c_2595,c_2597]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4564,plain,
% 11.11/1.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_4469,c_32]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_7,plain,
% 11.11/1.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.11/1.99      | ~ v1_relat_1(X1)
% 11.11/1.99      | ~ v1_relat_1(X0) ),
% 11.11/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1018,plain,
% 11.11/1.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.11/1.99      | v1_relat_1(X0) != iProver_top
% 11.11/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4569,plain,
% 11.11/1.99      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 11.11/1.99      | v1_relat_1(sK4) != iProver_top
% 11.11/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_4564,c_1018]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_34,plain,
% 11.11/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_37,plain,
% 11.11/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_9,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | v1_relat_1(X0) ),
% 11.11/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1078,plain,
% 11.11/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.11/1.99      | v1_relat_1(sK4) ),
% 11.11/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1132,plain,
% 11.11/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.11/1.99      | v1_relat_1(sK4) ),
% 11.11/1.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1133,plain,
% 11.11/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.11/1.99      | v1_relat_1(sK4) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1319,plain,
% 11.11/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.11/1.99      | v1_relat_1(sK3) ),
% 11.11/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1320,plain,
% 11.11/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.11/1.99      | v1_relat_1(sK3) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4915,plain,
% 11.11/1.99      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_4569,c_34,c_37,c_1133,c_1320]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4,plain,
% 11.11/1.99      ( ~ v5_relat_1(X0,X1)
% 11.11/1.99      | r1_tarski(k2_relat_1(X0),X1)
% 11.11/1.99      | ~ v1_relat_1(X0) ),
% 11.11/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_10,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | v5_relat_1(X0,X2) ),
% 11.11/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_349,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | r1_tarski(k2_relat_1(X3),X4)
% 11.11/1.99      | ~ v1_relat_1(X3)
% 11.11/1.99      | X0 != X3
% 11.11/1.99      | X2 != X4 ),
% 11.11/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_350,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | r1_tarski(k2_relat_1(X0),X2)
% 11.11/1.99      | ~ v1_relat_1(X0) ),
% 11.11/1.99      inference(unflattening,[status(thm)],[c_349]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_354,plain,
% 11.11/1.99      ( r1_tarski(k2_relat_1(X0),X2)
% 11.11/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.11/1.99      inference(global_propositional_subsumption,
% 11.11/1.99                [status(thm)],
% 11.11/1.99                [c_350,c_9]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_355,plain,
% 11.11/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.11/1.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.11/1.99      inference(renaming,[status(thm)],[c_354]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1006,plain,
% 11.11/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.11/1.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2333,plain,
% 11.11/1.99      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1011,c_1006]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_0,plain,
% 11.11/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.11/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1022,plain,
% 11.11/1.99      ( X0 = X1
% 11.11/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.11/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_2469,plain,
% 11.11/1.99      ( k2_relat_1(sK4) = sK2
% 11.11/1.99      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_2333,c_1022]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_4920,plain,
% 11.11/1.99      ( k2_relat_1(sK4) = sK2 ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_4915,c_2469]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1017,plain,
% 11.11/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.11/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.11/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.11/1.99  
% 11.11/1.99  cnf(c_1352,plain,
% 11.11/1.99      ( v1_relat_1(sK4) = iProver_top ),
% 11.11/1.99      inference(superposition,[status(thm)],[c_1011,c_1017]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6,plain,
% 11.68/1.99      ( ~ v1_relat_1(X0)
% 11.68/1.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1019,plain,
% 11.68/1.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1408,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1352,c_1019]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1016,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.68/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1773,plain,
% 11.68/1.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1011,c_1016]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18,plain,
% 11.68/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_27,negated_conjecture,
% 11.68/1.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 11.68/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_444,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.68/1.99      | sK4 != X0
% 11.68/1.99      | sK2 != X2
% 11.68/1.99      | sK1 != X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_445,plain,
% 11.68/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.68/1.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 11.68/1.99      | k1_xboole_0 = sK2 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_444]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23,negated_conjecture,
% 11.68/1.99      ( k1_xboole_0 != sK2 ),
% 11.68/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_447,plain,
% 11.68/1.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_445,c_26,c_23]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1775,plain,
% 11.68/1.99      ( k1_relat_1(sK4) = sK1 ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_1773,c_447]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2208,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_1408,c_1408,c_1775]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_32643,plain,
% 11.68/1.99      ( k10_relat_1(sK4,sK2) = sK1 ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_4920,c_2208]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2334,plain,
% 11.68/1.99      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1009,c_1006]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.68/1.99      | ~ v1_funct_1(X1)
% 11.68/1.99      | ~ v2_funct_1(X1)
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24,negated_conjecture,
% 11.68/1.99      ( v2_funct_1(sK4) ),
% 11.68/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_323,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.68/1.99      | ~ v1_funct_1(X1)
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 11.68/1.99      | sK4 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_324,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 11.68/1.99      | ~ v1_funct_1(sK4)
% 11.68/1.99      | ~ v1_relat_1(sK4)
% 11.68/1.99      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_323]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_328,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 11.68/1.99      | ~ v1_relat_1(sK4)
% 11.68/1.99      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_324,c_28]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1007,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 11.68/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_330,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 11.68/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1682,plain,
% 11.68/1.99      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 11.68/1.99      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_1007,c_37,c_330,c_1133]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1683,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_1682]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1963,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_1775,c_1683]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2473,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2334,c_1963]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1353,plain,
% 11.68/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1009,c_1017]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5,plain,
% 11.68/1.99      ( ~ v1_relat_1(X0)
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1020,plain,
% 11.68/1.99      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 11.68/1.99      | v1_relat_1(X0) != iProver_top
% 11.68/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1828,plain,
% 11.68/1.99      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1352,c_1020]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2833,plain,
% 11.68/1.99      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1353,c_1828]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3029,plain,
% 11.68/1.99      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_2473,c_2473,c_2833]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4567,plain,
% 11.68/1.99      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_4564,c_3029]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_33253,plain,
% 11.68/1.99      ( k2_relat_1(sK3) = sK1 ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_32643,c_4567]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1406,plain,
% 11.68/1.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1009,c_1015]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_22,negated_conjecture,
% 11.68/1.99      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 11.68/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1544,plain,
% 11.68/1.99      ( k2_relat_1(sK3) != sK1 ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_1406,c_22]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(contradiction,plain,
% 11.68/1.99      ( $false ),
% 11.68/1.99      inference(minisat,[status(thm)],[c_33253,c_1544]) ).
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  ------                               Statistics
% 11.68/1.99  
% 11.68/1.99  ------ General
% 11.68/1.99  
% 11.68/1.99  abstr_ref_over_cycles:                  0
% 11.68/1.99  abstr_ref_under_cycles:                 0
% 11.68/1.99  gc_basic_clause_elim:                   0
% 11.68/1.99  forced_gc_time:                         0
% 11.68/1.99  parsing_time:                           0.006
% 11.68/1.99  unif_index_cands_time:                  0.
% 11.68/1.99  unif_index_add_time:                    0.
% 11.68/1.99  orderings_time:                         0.
% 11.68/1.99  out_proof_time:                         0.013
% 11.68/1.99  total_time:                             1.034
% 11.68/1.99  num_of_symbols:                         54
% 11.68/1.99  num_of_terms:                           24910
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing
% 11.68/1.99  
% 11.68/1.99  num_of_splits:                          0
% 11.68/1.99  num_of_split_atoms:                     0
% 11.68/1.99  num_of_reused_defs:                     0
% 11.68/1.99  num_eq_ax_congr_red:                    14
% 11.68/1.99  num_of_sem_filtered_clauses:            1
% 11.68/1.99  num_of_subtypes:                        0
% 11.68/1.99  monotx_restored_types:                  0
% 11.68/1.99  sat_num_of_epr_types:                   0
% 11.68/1.99  sat_num_of_non_cyclic_types:            0
% 11.68/1.99  sat_guarded_non_collapsed_types:        0
% 11.68/1.99  num_pure_diseq_elim:                    0
% 11.68/1.99  simp_replaced_by:                       0
% 11.68/1.99  res_preprocessed:                       140
% 11.68/1.99  prep_upred:                             0
% 11.68/1.99  prep_unflattend:                        37
% 11.68/1.99  smt_new_axioms:                         0
% 11.68/1.99  pred_elim_cands:                        4
% 11.68/1.99  pred_elim:                              3
% 11.68/1.99  pred_elim_cl:                           5
% 11.68/1.99  pred_elim_cycles:                       5
% 11.68/1.99  merged_defs:                            0
% 11.68/1.99  merged_defs_ncl:                        0
% 11.68/1.99  bin_hyper_res:                          0
% 11.68/1.99  prep_cycles:                            4
% 11.68/1.99  pred_elim_time:                         0.003
% 11.68/1.99  splitting_time:                         0.
% 11.68/1.99  sem_filter_time:                        0.
% 11.68/1.99  monotx_time:                            0.001
% 11.68/1.99  subtype_inf_time:                       0.
% 11.68/1.99  
% 11.68/1.99  ------ Problem properties
% 11.68/1.99  
% 11.68/1.99  clauses:                                26
% 11.68/1.99  conjectures:                            7
% 11.68/1.99  epr:                                    5
% 11.68/1.99  horn:                                   23
% 11.68/1.99  ground:                                 13
% 11.68/1.99  unary:                                  9
% 11.68/1.99  binary:                                 6
% 11.68/1.99  lits:                                   62
% 11.68/1.99  lits_eq:                                23
% 11.68/1.99  fd_pure:                                0
% 11.68/1.99  fd_pseudo:                              0
% 11.68/1.99  fd_cond:                                0
% 11.68/1.99  fd_pseudo_cond:                         1
% 11.68/1.99  ac_symbols:                             0
% 11.68/1.99  
% 11.68/1.99  ------ Propositional Solver
% 11.68/1.99  
% 11.68/1.99  prop_solver_calls:                      35
% 11.68/1.99  prop_fast_solver_calls:                 2501
% 11.68/1.99  smt_solver_calls:                       0
% 11.68/1.99  smt_fast_solver_calls:                  0
% 11.68/1.99  prop_num_of_clauses:                    15526
% 11.68/1.99  prop_preprocess_simplified:             19027
% 11.68/1.99  prop_fo_subsumed:                       570
% 11.68/1.99  prop_solver_time:                       0.
% 11.68/1.99  smt_solver_time:                        0.
% 11.68/1.99  smt_fast_solver_time:                   0.
% 11.68/1.99  prop_fast_solver_time:                  0.
% 11.68/1.99  prop_unsat_core_time:                   0.002
% 11.68/1.99  
% 11.68/1.99  ------ QBF
% 11.68/1.99  
% 11.68/1.99  qbf_q_res:                              0
% 11.68/1.99  qbf_num_tautologies:                    0
% 11.68/1.99  qbf_prep_cycles:                        0
% 11.68/1.99  
% 11.68/1.99  ------ BMC1
% 11.68/1.99  
% 11.68/1.99  bmc1_current_bound:                     -1
% 11.68/1.99  bmc1_last_solved_bound:                 -1
% 11.68/1.99  bmc1_unsat_core_size:                   -1
% 11.68/1.99  bmc1_unsat_core_parents_size:           -1
% 11.68/1.99  bmc1_merge_next_fun:                    0
% 11.68/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation
% 11.68/1.99  
% 11.68/1.99  inst_num_of_clauses:                    4390
% 11.68/1.99  inst_num_in_passive:                    1906
% 11.68/1.99  inst_num_in_active:                     2286
% 11.68/1.99  inst_num_in_unprocessed:                198
% 11.68/1.99  inst_num_of_loops:                      2420
% 11.68/1.99  inst_num_of_learning_restarts:          0
% 11.68/1.99  inst_num_moves_active_passive:          126
% 11.68/1.99  inst_lit_activity:                      0
% 11.68/1.99  inst_lit_activity_moves:                0
% 11.68/1.99  inst_num_tautologies:                   0
% 11.68/1.99  inst_num_prop_implied:                  0
% 11.68/1.99  inst_num_existing_simplified:           0
% 11.68/1.99  inst_num_eq_res_simplified:             0
% 11.68/1.99  inst_num_child_elim:                    0
% 11.68/1.99  inst_num_of_dismatching_blockings:      1868
% 11.68/1.99  inst_num_of_non_proper_insts:           6406
% 11.68/1.99  inst_num_of_duplicates:                 0
% 11.68/1.99  inst_inst_num_from_inst_to_res:         0
% 11.68/1.99  inst_dismatching_checking_time:         0.
% 11.68/1.99  
% 11.68/1.99  ------ Resolution
% 11.68/1.99  
% 11.68/1.99  res_num_of_clauses:                     0
% 11.68/1.99  res_num_in_passive:                     0
% 11.68/1.99  res_num_in_active:                      0
% 11.68/1.99  res_num_of_loops:                       144
% 11.68/1.99  res_forward_subset_subsumed:            785
% 11.68/1.99  res_backward_subset_subsumed:           0
% 11.68/1.99  res_forward_subsumed:                   0
% 11.68/1.99  res_backward_subsumed:                  0
% 11.68/1.99  res_forward_subsumption_resolution:     0
% 11.68/1.99  res_backward_subsumption_resolution:    0
% 11.68/1.99  res_clause_to_clause_subsumption:       3625
% 11.68/1.99  res_orphan_elimination:                 0
% 11.68/1.99  res_tautology_del:                      542
% 11.68/1.99  res_num_eq_res_simplified:              0
% 11.68/1.99  res_num_sel_changes:                    0
% 11.68/1.99  res_moves_from_active_to_pass:          0
% 11.68/1.99  
% 11.68/1.99  ------ Superposition
% 11.68/1.99  
% 11.68/1.99  sup_time_total:                         0.
% 11.68/1.99  sup_time_generating:                    0.
% 11.68/1.99  sup_time_sim_full:                      0.
% 11.68/1.99  sup_time_sim_immed:                     0.
% 11.68/1.99  
% 11.68/1.99  sup_num_of_clauses:                     1714
% 11.68/1.99  sup_num_in_active:                      458
% 11.68/1.99  sup_num_in_passive:                     1256
% 11.68/1.99  sup_num_of_loops:                       483
% 11.68/1.99  sup_fw_superposition:                   1027
% 11.68/1.99  sup_bw_superposition:                   885
% 11.68/1.99  sup_immediate_simplified:               554
% 11.68/1.99  sup_given_eliminated:                   1
% 11.68/1.99  comparisons_done:                       0
% 11.68/1.99  comparisons_avoided:                    3
% 11.68/1.99  
% 11.68/1.99  ------ Simplifications
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  sim_fw_subset_subsumed:                 6
% 11.68/1.99  sim_bw_subset_subsumed:                 74
% 11.68/1.99  sim_fw_subsumed:                        4
% 11.68/1.99  sim_bw_subsumed:                        0
% 11.68/1.99  sim_fw_subsumption_res:                 0
% 11.68/1.99  sim_bw_subsumption_res:                 0
% 11.68/1.99  sim_tautology_del:                      0
% 11.68/1.99  sim_eq_tautology_del:                   98
% 11.68/1.99  sim_eq_res_simp:                        0
% 11.68/1.99  sim_fw_demodulated:                     22
% 11.68/1.99  sim_bw_demodulated:                     13
% 11.68/1.99  sim_light_normalised:                   593
% 11.68/1.99  sim_joinable_taut:                      0
% 11.68/1.99  sim_joinable_simp:                      0
% 11.68/1.99  sim_ac_normalised:                      0
% 11.68/1.99  sim_smt_subsumption:                    0
% 11.68/1.99  
%------------------------------------------------------------------------------
