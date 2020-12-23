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
% DateTime   : Thu Dec  3 12:01:41 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 636 expanded)
%              Number of clauses        :  102 ( 198 expanded)
%              Number of leaves         :   19 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  514 (4155 expanded)
%              Number of equality atoms :  230 (1386 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f47,f46])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f45,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1560,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1143])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1137,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1559,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1143])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1145,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3290,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1559,c_1145])).

cnf(c_5266,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1560,c_3290])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_411,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_11])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_411])).

cnf(c_1131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_2086,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1131])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1141,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2363,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1137,c_1141])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_502,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_504,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_29,c_26])).

cnf(c_2368,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2363,c_504])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_380,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_381,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_385,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_31])).

cnf(c_1132,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_387,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1325,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_1807,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_40,c_387,c_1325])).

cnf(c_1808,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1807])).

cnf(c_2467,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2368,c_1808])).

cnf(c_5252,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2086,c_2467])).

cnf(c_5281,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5266,c_5252])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1140,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3538,plain,
    ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1140])).

cnf(c_5831,plain,
    ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_3538])).

cnf(c_6068,plain,
    ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1135,c_5831])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1139,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3517,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1139])).

cnf(c_4081,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1135,c_3517])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1138,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3830,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1138])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5116,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_38])).

cnf(c_5117,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5116])).

cnf(c_5127,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_5117])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_3132,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_5158,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5127,c_34,c_32,c_31,c_29,c_3132])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5161,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5158,c_28])).

cnf(c_6077,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6068,c_4081,c_5161])).

cnf(c_2085,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1131])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1147,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2474,plain,
    ( k3_xboole_0(k2_relat_1(sK4),sK2) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2085,c_1147])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1144,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2191,plain,
    ( k10_relat_1(sK4,k3_xboole_0(k2_relat_1(sK4),X0)) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1559,c_1144])).

cnf(c_5222,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k10_relat_1(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2474,c_2191])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_9])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_13,c_11,c_9])).

cnf(c_1133,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_3280,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_1137,c_1133])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1146,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1664,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1559,c_1146])).

cnf(c_3870,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3280,c_1664])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1148,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1815,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1148,c_1808])).

cnf(c_5107,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1815,c_2368])).

cnf(c_5214,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3870,c_5107])).

cnf(c_13589,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5222,c_5214])).

cnf(c_15700,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5281,c_6077,c_13589])).

cnf(c_2203,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1135,c_1140])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3021,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_2203,c_25])).

cnf(c_15702,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15700,c_3021])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.97/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.97  
% 3.97/0.97  ------  iProver source info
% 3.97/0.97  
% 3.97/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.97  git: non_committed_changes: false
% 3.97/0.97  git: last_make_outside_of_git: false
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     num_symb
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       true
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  ------ Parsing...
% 3.97/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.97  ------ Proving...
% 3.97/0.97  ------ Problem Properties 
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  clauses                                 28
% 3.97/0.97  conjectures                             7
% 3.97/0.97  EPR                                     5
% 3.97/0.97  Horn                                    25
% 3.97/0.97  unary                                   9
% 3.97/0.97  binary                                  9
% 3.97/0.97  lits                                    61
% 3.97/0.97  lits eq                                 27
% 3.97/0.97  fd_pure                                 0
% 3.97/0.97  fd_pseudo                               0
% 3.97/0.97  fd_cond                                 0
% 3.97/0.97  fd_pseudo_cond                          1
% 3.97/0.97  AC symbols                              0
% 3.97/0.97  
% 3.97/0.97  ------ Schedule dynamic 5 is on 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  Current options:
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     none
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       false
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ Proving...
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS status Theorem for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97   Resolution empty clause
% 3.97/0.97  
% 3.97/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  fof(f17,conjecture,(
% 3.97/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f18,negated_conjecture,(
% 3.97/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.97/0.97    inference(negated_conjecture,[],[f17])).
% 3.97/0.97  
% 3.97/0.97  fof(f40,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.97/0.97    inference(ennf_transformation,[],[f18])).
% 3.97/0.97  
% 3.97/0.97  fof(f41,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.97/0.97    inference(flattening,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f47,plain,(
% 3.97/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f46,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f48,plain,(
% 3.97/0.97    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f47,f46])).
% 3.97/0.97  
% 3.97/0.97  fof(f76,plain,(
% 3.97/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f9,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f28,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f9])).
% 3.97/0.97  
% 3.97/0.97  fof(f60,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f28])).
% 3.97/0.97  
% 3.97/0.97  fof(f79,plain,(
% 3.97/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f5,axiom,(
% 3.97/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f22,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.97/0.97    inference(ennf_transformation,[],[f5])).
% 3.97/0.97  
% 3.97/0.97  fof(f56,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f22])).
% 3.97/0.97  
% 3.97/0.97  fof(f3,axiom,(
% 3.97/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f20,plain,(
% 3.97/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f3])).
% 3.97/0.97  
% 3.97/0.97  fof(f44,plain,(
% 3.97/0.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(nnf_transformation,[],[f20])).
% 3.97/0.97  
% 3.97/0.97  fof(f53,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f44])).
% 3.97/0.97  
% 3.97/0.97  fof(f10,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f29,plain,(
% 3.97/0.97    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f10])).
% 3.97/0.97  
% 3.97/0.97  fof(f62,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f29])).
% 3.97/0.97  
% 3.97/0.97  fof(f12,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f32,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f12])).
% 3.97/0.97  
% 3.97/0.97  fof(f64,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f32])).
% 3.97/0.97  
% 3.97/0.97  fof(f15,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f36,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f15])).
% 3.97/0.97  
% 3.97/0.97  fof(f37,plain,(
% 3.97/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(flattening,[],[f36])).
% 3.97/0.97  
% 3.97/0.97  fof(f45,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(nnf_transformation,[],[f37])).
% 3.97/0.97  
% 3.97/0.97  fof(f67,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f45])).
% 3.97/0.97  
% 3.97/0.97  fof(f78,plain,(
% 3.97/0.97    v1_funct_2(sK4,sK1,sK2)),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f82,plain,(
% 3.97/0.97    k1_xboole_0 != sK2),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f8,axiom,(
% 3.97/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f26,plain,(
% 3.97/0.97    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.97/0.97    inference(ennf_transformation,[],[f8])).
% 3.97/0.97  
% 3.97/0.97  fof(f27,plain,(
% 3.97/0.97    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(flattening,[],[f26])).
% 3.97/0.97  
% 3.97/0.97  fof(f59,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f27])).
% 3.97/0.97  
% 3.97/0.97  fof(f81,plain,(
% 3.97/0.97    v2_funct_1(sK4)),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f77,plain,(
% 3.97/0.97    v1_funct_1(sK4)),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f11,axiom,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f30,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.97/0.97    inference(ennf_transformation,[],[f11])).
% 3.97/0.97  
% 3.97/0.97  fof(f31,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(flattening,[],[f30])).
% 3.97/0.97  
% 3.97/0.97  fof(f63,plain,(
% 3.97/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f31])).
% 3.97/0.97  
% 3.97/0.97  fof(f13,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f33,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f13])).
% 3.97/0.97  
% 3.97/0.97  fof(f65,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f33])).
% 3.97/0.97  
% 3.97/0.97  fof(f14,axiom,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f34,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.97/0.97    inference(ennf_transformation,[],[f14])).
% 3.97/0.97  
% 3.97/0.97  fof(f35,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(flattening,[],[f34])).
% 3.97/0.97  
% 3.97/0.97  fof(f66,plain,(
% 3.97/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f35])).
% 3.97/0.97  
% 3.97/0.97  fof(f16,axiom,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f38,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.97/0.97    inference(ennf_transformation,[],[f16])).
% 3.97/0.97  
% 3.97/0.97  fof(f39,plain,(
% 3.97/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.97/0.97    inference(flattening,[],[f38])).
% 3.97/0.97  
% 3.97/0.97  fof(f73,plain,(
% 3.97/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f39])).
% 3.97/0.97  
% 3.97/0.97  fof(f74,plain,(
% 3.97/0.97    v1_funct_1(sK3)),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f80,plain,(
% 3.97/0.97    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  fof(f2,axiom,(
% 3.97/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f19,plain,(
% 3.97/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f2])).
% 3.97/0.97  
% 3.97/0.97  fof(f52,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f19])).
% 3.97/0.97  
% 3.97/0.97  fof(f6,axiom,(
% 3.97/0.97    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f23,plain,(
% 3.97/0.97    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f6])).
% 3.97/0.97  
% 3.97/0.97  fof(f57,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f23])).
% 3.97/0.97  
% 3.97/0.97  fof(f61,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f29])).
% 3.97/0.97  
% 3.97/0.97  fof(f7,axiom,(
% 3.97/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f24,plain,(
% 3.97/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.97/0.97    inference(ennf_transformation,[],[f7])).
% 3.97/0.97  
% 3.97/0.97  fof(f25,plain,(
% 3.97/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(flattening,[],[f24])).
% 3.97/0.97  
% 3.97/0.97  fof(f58,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f25])).
% 3.97/0.97  
% 3.97/0.97  fof(f4,axiom,(
% 3.97/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f21,plain,(
% 3.97/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f4])).
% 3.97/0.97  
% 3.97/0.97  fof(f55,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f21])).
% 3.97/0.97  
% 3.97/0.97  fof(f1,axiom,(
% 3.97/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f42,plain,(
% 3.97/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.97    inference(nnf_transformation,[],[f1])).
% 3.97/0.97  
% 3.97/0.97  fof(f43,plain,(
% 3.97/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.97    inference(flattening,[],[f42])).
% 3.97/0.97  
% 3.97/0.97  fof(f50,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.97/0.97    inference(cnf_transformation,[],[f43])).
% 3.97/0.97  
% 3.97/0.97  fof(f84,plain,(
% 3.97/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.97/0.97    inference(equality_resolution,[],[f50])).
% 3.97/0.97  
% 3.97/0.97  fof(f83,plain,(
% 3.97/0.97    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.97/0.97    inference(cnf_transformation,[],[f48])).
% 3.97/0.97  
% 3.97/0.97  cnf(c_32,negated_conjecture,
% 3.97/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.97/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1135,plain,
% 3.97/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1143,plain,
% 3.97/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1560,plain,
% 3.97/0.97      ( v1_relat_1(sK3) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_1143]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_29,negated_conjecture,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.97/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1137,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1559,plain,
% 3.97/0.97      ( v1_relat_1(sK4) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1143]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7,plain,
% 3.97/0.97      ( ~ v1_relat_1(X0)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1145,plain,
% 3.97/0.97      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3290,plain,
% 3.97/0.97      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1559,c_1145]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5266,plain,
% 3.97/0.97      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1560,c_3290]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5,plain,
% 3.97/0.97      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_12,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_406,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | r1_tarski(k2_relat_1(X3),X4)
% 3.97/0.97      | ~ v1_relat_1(X3)
% 3.97/0.97      | X0 != X3
% 3.97/0.97      | X2 != X4 ),
% 3.97/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_407,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | r1_tarski(k2_relat_1(X0),X2)
% 3.97/0.97      | ~ v1_relat_1(X0) ),
% 3.97/0.97      inference(unflattening,[status(thm)],[c_406]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_411,plain,
% 3.97/0.97      ( r1_tarski(k2_relat_1(X0),X2)
% 3.97/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.97/0.97      inference(global_propositional_subsumption,[status(thm)],[c_407,c_11]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_412,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_411]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1131,plain,
% 3.97/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.97/0.97      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2086,plain,
% 3.97/0.97      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_1131]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_15,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1141,plain,
% 3.97/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2363,plain,
% 3.97/0.97      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1141]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_23,plain,
% 3.97/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.97/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.97/0.97      | k1_xboole_0 = X2 ),
% 3.97/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_30,negated_conjecture,
% 3.97/0.97      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_501,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.97/0.97      | sK4 != X0
% 3.97/0.97      | sK2 != X2
% 3.97/0.97      | sK1 != X1
% 3.97/0.97      | k1_xboole_0 = X2 ),
% 3.97/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_502,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.97/0.97      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.97/0.97      | k1_xboole_0 = sK2 ),
% 3.97/0.97      inference(unflattening,[status(thm)],[c_501]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_26,negated_conjecture,
% 3.97/0.97      ( k1_xboole_0 != sK2 ),
% 3.97/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_504,plain,
% 3.97/0.97      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_502,c_29,c_26]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2368,plain,
% 3.97/0.97      ( k1_relat_1(sK4) = sK1 ),
% 3.97/0.97      inference(light_normalisation,[status(thm)],[c_2363,c_504]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.97/0.97      | ~ v1_funct_1(X1)
% 3.97/0.97      | ~ v2_funct_1(X1)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.97/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_27,negated_conjecture,
% 3.97/0.97      ( v2_funct_1(sK4) ),
% 3.97/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_380,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.97/0.97      | ~ v1_funct_1(X1)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.97/0.97      | sK4 != X1 ),
% 3.97/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_381,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_relat_1(sK4)
% 3.97/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.97/0.97      inference(unflattening,[status(thm)],[c_380]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_31,negated_conjecture,
% 3.97/0.97      ( v1_funct_1(sK4) ),
% 3.97/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_385,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.97/0.97      | ~ v1_relat_1(sK4)
% 3.97/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.97/0.97      inference(global_propositional_subsumption,[status(thm)],[c_381,c_31]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1132,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.97/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_40,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_387,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.97/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1324,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.97/0.97      | v1_relat_1(sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1325,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1807,plain,
% 3.97/0.97      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_1132,c_40,c_387,c_1325]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1808,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.97/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_1807]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2467,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.97/0.97      | r1_tarski(X0,sK1) != iProver_top ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_2368,c_1808]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5252,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2086,c_2467]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5281,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_5266,c_5252]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_14,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.97/0.97      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.97/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1142,plain,
% 3.97/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.97/0.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.97/0.97      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1140,plain,
% 3.97/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3538,plain,
% 3.97/0.97      ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
% 3.97/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.97/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1142,c_1140]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5831,plain,
% 3.97/0.97      ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_3538]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6068,plain,
% 3.97/0.97      ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_5831]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_17,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.97/0.97      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1139,plain,
% 3.97/0.97      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.97/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.97/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3517,plain,
% 3.97/0.97      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1139]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4081,plain,
% 3.97/0.97      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_3517]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_24,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_funct_1(X3)
% 3.97/0.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1138,plain,
% 3.97/0.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.97/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.97/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.97/0.97      | v1_funct_1(X5) != iProver_top
% 3.97/0.97      | v1_funct_1(X4) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3830,plain,
% 3.97/0.97      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.97/0.97      | v1_funct_1(X2) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1138]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_38,plain,
% 3.97/0.97      ( v1_funct_1(sK4) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5116,plain,
% 3.97/0.97      ( v1_funct_1(X2) != iProver_top
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.97/0.97      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.97/0.97      inference(global_propositional_subsumption,[status(thm)],[c_3830,c_38]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5117,plain,
% 3.97/0.97      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.97/0.97      | v1_funct_1(X2) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_5116]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5127,plain,
% 3.97/0.97      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.97/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_5117]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_34,negated_conjecture,
% 3.97/0.97      ( v1_funct_1(sK3) ),
% 3.97/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1422,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_24]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1644,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.97/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_funct_1(sK3)
% 3.97/0.97      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2058,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.97/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_funct_1(sK3)
% 3.97/0.97      | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1644]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3132,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.97/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_funct_1(sK3)
% 3.97/0.97      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2058]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5158,plain,
% 3.97/0.97      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_5127,c_34,c_32,c_31,c_29,c_3132]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_28,negated_conjecture,
% 3.97/0.97      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.97/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5161,plain,
% 3.97/0.97      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_5158,c_28]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6077,plain,
% 3.97/0.97      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.97/0.97      inference(light_normalisation,[status(thm)],[c_6068,c_4081,c_5161]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2085,plain,
% 3.97/0.97      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1131]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.97/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1147,plain,
% 3.97/0.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2474,plain,
% 3.97/0.97      ( k3_xboole_0(k2_relat_1(sK4),sK2) = k2_relat_1(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2085,c_1147]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8,plain,
% 3.97/0.97      ( ~ v1_relat_1(X0)
% 3.97/0.97      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1144,plain,
% 3.97/0.97      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2191,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k3_xboole_0(k2_relat_1(sK4),X0)) = k10_relat_1(sK4,X0) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1559,c_1144]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5222,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k10_relat_1(sK4,sK2) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2474,c_2191]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_13,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_9,plain,
% 3.97/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.97/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_360,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.97/0.97      inference(resolution,[status(thm)],[c_13,c_9]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_364,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_360,c_13,c_11,c_9]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1133,plain,
% 3.97/0.97      ( k7_relat_1(X0,X1) = X0
% 3.97/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3280,plain,
% 3.97/0.97      ( k7_relat_1(sK4,sK1) = sK4 ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1137,c_1133]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6,plain,
% 3.97/0.97      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1146,plain,
% 3.97/0.97      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1664,plain,
% 3.97/0.97      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1559,c_1146]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3870,plain,
% 3.97/0.97      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3280,c_1664]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f84]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1148,plain,
% 3.97/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1815,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1148,c_1808]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5107,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1 ),
% 3.97/0.97      inference(light_normalisation,[status(thm)],[c_1815,c_2368]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5214,plain,
% 3.97/0.97      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_3870,c_5107]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_13589,plain,
% 3.97/0.97      ( k10_relat_1(sK4,sK2) = sK1 ),
% 3.97/0.97      inference(light_normalisation,[status(thm)],[c_5222,c_5214]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_15700,plain,
% 3.97/0.97      ( k2_relat_1(sK3) = sK1 ),
% 3.97/0.97      inference(light_normalisation,[status(thm)],[c_5281,c_6077,c_13589]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2203,plain,
% 3.97/0.97      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1135,c_1140]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_25,negated_conjecture,
% 3.97/0.97      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.97/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3021,plain,
% 3.97/0.97      ( k2_relat_1(sK3) != sK1 ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_2203,c_25]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_15702,plain,
% 3.97/0.97      ( $false ),
% 3.97/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_15700,c_3021]) ).
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  ------                               Statistics
% 3.97/0.97  
% 3.97/0.97  ------ General
% 3.97/0.97  
% 3.97/0.97  abstr_ref_over_cycles:                  0
% 3.97/0.97  abstr_ref_under_cycles:                 0
% 3.97/0.97  gc_basic_clause_elim:                   0
% 3.97/0.97  forced_gc_time:                         0
% 3.97/0.97  parsing_time:                           0.01
% 3.97/0.97  unif_index_cands_time:                  0.
% 3.97/0.97  unif_index_add_time:                    0.
% 3.97/0.97  orderings_time:                         0.
% 3.97/0.97  out_proof_time:                         0.012
% 3.97/0.97  total_time:                             0.494
% 3.97/0.97  num_of_symbols:                         58
% 3.97/0.97  num_of_terms:                           16365
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing
% 3.97/0.97  
% 3.97/0.97  num_of_splits:                          0
% 3.97/0.97  num_of_split_atoms:                     0
% 3.97/0.97  num_of_reused_defs:                     0
% 3.97/0.97  num_eq_ax_congr_red:                    43
% 3.97/0.97  num_of_sem_filtered_clauses:            1
% 3.97/0.97  num_of_subtypes:                        0
% 3.97/0.97  monotx_restored_types:                  0
% 3.97/0.97  sat_num_of_epr_types:                   0
% 3.97/0.97  sat_num_of_non_cyclic_types:            0
% 3.97/0.97  sat_guarded_non_collapsed_types:        0
% 3.97/0.97  num_pure_diseq_elim:                    0
% 3.97/0.97  simp_replaced_by:                       0
% 3.97/0.97  res_preprocessed:                       151
% 3.97/0.97  prep_upred:                             0
% 3.97/0.97  prep_unflattend:                        37
% 3.97/0.97  smt_new_axioms:                         0
% 3.97/0.97  pred_elim_cands:                        4
% 3.97/0.97  pred_elim:                              4
% 3.97/0.97  pred_elim_cl:                           6
% 3.97/0.97  pred_elim_cycles:                       6
% 3.97/0.97  merged_defs:                            0
% 3.97/0.97  merged_defs_ncl:                        0
% 3.97/0.97  bin_hyper_res:                          0
% 3.97/0.97  prep_cycles:                            4
% 3.97/0.97  pred_elim_time:                         0.005
% 3.97/0.97  splitting_time:                         0.
% 3.97/0.97  sem_filter_time:                        0.
% 3.97/0.97  monotx_time:                            0.
% 3.97/0.97  subtype_inf_time:                       0.
% 3.97/0.97  
% 3.97/0.97  ------ Problem properties
% 3.97/0.97  
% 3.97/0.97  clauses:                                28
% 3.97/0.97  conjectures:                            7
% 3.97/0.97  epr:                                    5
% 3.97/0.97  horn:                                   25
% 3.97/0.97  ground:                                 13
% 3.97/0.97  unary:                                  9
% 3.97/0.97  binary:                                 9
% 3.97/0.97  lits:                                   61
% 3.97/0.97  lits_eq:                                27
% 3.97/0.97  fd_pure:                                0
% 3.97/0.97  fd_pseudo:                              0
% 3.97/0.97  fd_cond:                                0
% 3.97/0.97  fd_pseudo_cond:                         1
% 3.97/0.97  ac_symbols:                             0
% 3.97/0.97  
% 3.97/0.97  ------ Propositional Solver
% 3.97/0.97  
% 3.97/0.97  prop_solver_calls:                      30
% 3.97/0.97  prop_fast_solver_calls:                 1193
% 3.97/0.97  smt_solver_calls:                       0
% 3.97/0.97  smt_fast_solver_calls:                  0
% 3.97/0.97  prop_num_of_clauses:                    6534
% 3.97/0.97  prop_preprocess_simplified:             12188
% 3.97/0.97  prop_fo_subsumed:                       43
% 3.97/0.97  prop_solver_time:                       0.
% 3.97/0.97  smt_solver_time:                        0.
% 3.97/0.97  smt_fast_solver_time:                   0.
% 3.97/0.97  prop_fast_solver_time:                  0.
% 3.97/0.97  prop_unsat_core_time:                   0.
% 3.97/0.97  
% 3.97/0.97  ------ QBF
% 3.97/0.97  
% 3.97/0.97  qbf_q_res:                              0
% 3.97/0.97  qbf_num_tautologies:                    0
% 3.97/0.97  qbf_prep_cycles:                        0
% 3.97/0.97  
% 3.97/0.97  ------ BMC1
% 3.97/0.97  
% 3.97/0.97  bmc1_current_bound:                     -1
% 3.97/0.97  bmc1_last_solved_bound:                 -1
% 3.97/0.97  bmc1_unsat_core_size:                   -1
% 3.97/0.97  bmc1_unsat_core_parents_size:           -1
% 3.97/0.97  bmc1_merge_next_fun:                    0
% 3.97/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation
% 3.97/0.97  
% 3.97/0.97  inst_num_of_clauses:                    1783
% 3.97/0.97  inst_num_in_passive:                    461
% 3.97/0.97  inst_num_in_active:                     1156
% 3.97/0.97  inst_num_in_unprocessed:                166
% 3.97/0.97  inst_num_of_loops:                      1200
% 3.97/0.97  inst_num_of_learning_restarts:          0
% 3.97/0.97  inst_num_moves_active_passive:          41
% 3.97/0.97  inst_lit_activity:                      0
% 3.97/0.97  inst_lit_activity_moves:                1
% 3.97/0.97  inst_num_tautologies:                   0
% 3.97/0.97  inst_num_prop_implied:                  0
% 3.97/0.97  inst_num_existing_simplified:           0
% 3.97/0.97  inst_num_eq_res_simplified:             0
% 3.97/0.97  inst_num_child_elim:                    0
% 3.97/0.97  inst_num_of_dismatching_blockings:      513
% 3.97/0.97  inst_num_of_non_proper_insts:           1519
% 3.97/0.97  inst_num_of_duplicates:                 0
% 3.97/0.97  inst_inst_num_from_inst_to_res:         0
% 3.97/0.97  inst_dismatching_checking_time:         0.
% 3.97/0.97  
% 3.97/0.97  ------ Resolution
% 3.97/0.97  
% 3.97/0.97  res_num_of_clauses:                     0
% 3.97/0.97  res_num_in_passive:                     0
% 3.97/0.97  res_num_in_active:                      0
% 3.97/0.97  res_num_of_loops:                       155
% 3.97/0.97  res_forward_subset_subsumed:            78
% 3.97/0.97  res_backward_subset_subsumed:           0
% 3.97/0.97  res_forward_subsumed:                   0
% 3.97/0.97  res_backward_subsumed:                  0
% 3.97/0.97  res_forward_subsumption_resolution:     0
% 3.97/0.97  res_backward_subsumption_resolution:    0
% 3.97/0.97  res_clause_to_clause_subsumption:       1423
% 3.97/0.97  res_orphan_elimination:                 0
% 3.97/0.97  res_tautology_del:                      100
% 3.97/0.97  res_num_eq_res_simplified:              0
% 3.97/0.97  res_num_sel_changes:                    0
% 3.97/0.97  res_moves_from_active_to_pass:          0
% 3.97/0.97  
% 3.97/0.97  ------ Superposition
% 3.97/0.97  
% 3.97/0.97  sup_time_total:                         0.
% 3.97/0.97  sup_time_generating:                    0.
% 3.97/0.97  sup_time_sim_full:                      0.
% 3.97/0.97  sup_time_sim_immed:                     0.
% 3.97/0.97  
% 3.97/0.97  sup_num_of_clauses:                     709
% 3.97/0.97  sup_num_in_active:                      233
% 3.97/0.97  sup_num_in_passive:                     476
% 3.97/0.97  sup_num_of_loops:                       239
% 3.97/0.97  sup_fw_superposition:                   317
% 3.97/0.97  sup_bw_superposition:                   425
% 3.97/0.97  sup_immediate_simplified:               180
% 3.97/0.97  sup_given_eliminated:                   0
% 3.97/0.97  comparisons_done:                       0
% 3.97/0.97  comparisons_avoided:                    3
% 3.97/0.97  
% 3.97/0.97  ------ Simplifications
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  sim_fw_subset_subsumed:                 4
% 3.97/0.97  sim_bw_subset_subsumed:                 0
% 3.97/0.97  sim_fw_subsumed:                        10
% 3.97/0.97  sim_bw_subsumed:                        0
% 3.97/0.97  sim_fw_subsumption_res:                 1
% 3.97/0.97  sim_bw_subsumption_res:                 0
% 3.97/0.97  sim_tautology_del:                      0
% 3.97/0.97  sim_eq_tautology_del:                   14
% 3.97/0.97  sim_eq_res_simp:                        0
% 3.97/0.97  sim_fw_demodulated:                     0
% 3.97/0.97  sim_bw_demodulated:                     6
% 3.97/0.97  sim_light_normalised:                   186
% 3.97/0.97  sim_joinable_taut:                      0
% 3.97/0.97  sim_joinable_simp:                      0
% 3.97/0.97  sim_ac_normalised:                      0
% 3.97/0.97  sim_smt_subsumption:                    0
% 3.97/0.97  
%------------------------------------------------------------------------------
