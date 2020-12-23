%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:40 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  173 (1561 expanded)
%              Number of clauses        :  104 ( 490 expanded)
%              Number of leaves         :   17 ( 373 expanded)
%              Depth                    :   20
%              Number of atoms          :  524 (10514 expanded)
%              Number of equality atoms :  242 (3576 expanded)
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f43,f42])).

fof(f71,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1043,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1055,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1051,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2387,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1051])).

cnf(c_3417,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,k2_relat_1(sK4))) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_2387])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1044,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1050,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1387,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1050])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1053,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1447,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1387,c_1053])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1049,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1839,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1044,c_1049])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_456,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_458,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_27,c_24])).

cnf(c_1841,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1839,c_458])).

cnf(c_2255,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1447,c_1447,c_1841])).

cnf(c_3422,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3417,c_2255])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1113,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1167,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_1168,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_3853,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3422,c_38,c_1168])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_29])).

cnf(c_1040,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_341,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1740,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_38,c_341,c_1168])).

cnf(c_1741,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1740])).

cnf(c_1746,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1055,c_1741])).

cnf(c_2294,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1746,c_1746,c_1841])).

cnf(c_3855,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3853,c_2294])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1042,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1048,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2510,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1048])).

cnf(c_5401,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_2510])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5751,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5401,c_36])).

cnf(c_5752,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5751])).

cnf(c_5759,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_5752])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1045,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2458,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1045])).

cnf(c_2575,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2458,c_36])).

cnf(c_2576,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2575])).

cnf(c_2583,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_2576])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2657,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2583,c_33])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2659,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2657,c_26])).

cnf(c_5764,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5759,c_2657,c_2659])).

cnf(c_5871,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5764,c_33])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1052,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5879,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5871,c_1052])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1355,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1354])).

cnf(c_6193,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5879,c_35,c_38,c_1168,c_1355])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_365,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_10])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_1039,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_2382,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1039])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1056,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2530,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_1056])).

cnf(c_6199,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_6193,c_2530])).

cnf(c_2383,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1039])).

cnf(c_2013,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1841,c_1741])).

cnf(c_3253,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2383,c_2013])).

cnf(c_1388,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1050])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1054,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1894,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1054])).

cnf(c_2297,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1388,c_1894])).

cnf(c_3254,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3253,c_2297])).

cnf(c_8795,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3254,c_3254,c_5871])).

cnf(c_13054,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3855,c_3855,c_6199,c_8795])).

cnf(c_1445,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1042,c_1048])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1604,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1445,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13054,c_1604])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.98/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.03  
% 3.98/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/1.03  
% 3.98/1.03  ------  iProver source info
% 3.98/1.03  
% 3.98/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.98/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/1.03  git: non_committed_changes: false
% 3.98/1.03  git: last_make_outside_of_git: false
% 3.98/1.03  
% 3.98/1.03  ------ 
% 3.98/1.03  
% 3.98/1.03  ------ Input Options
% 3.98/1.03  
% 3.98/1.03  --out_options                           all
% 3.98/1.03  --tptp_safe_out                         true
% 3.98/1.03  --problem_path                          ""
% 3.98/1.03  --include_path                          ""
% 3.98/1.03  --clausifier                            res/vclausify_rel
% 3.98/1.03  --clausifier_options                    ""
% 3.98/1.03  --stdin                                 false
% 3.98/1.03  --stats_out                             all
% 3.98/1.03  
% 3.98/1.03  ------ General Options
% 3.98/1.03  
% 3.98/1.03  --fof                                   false
% 3.98/1.03  --time_out_real                         305.
% 3.98/1.03  --time_out_virtual                      -1.
% 3.98/1.03  --symbol_type_check                     false
% 3.98/1.03  --clausify_out                          false
% 3.98/1.03  --sig_cnt_out                           false
% 3.98/1.03  --trig_cnt_out                          false
% 3.98/1.03  --trig_cnt_out_tolerance                1.
% 3.98/1.03  --trig_cnt_out_sk_spl                   false
% 3.98/1.03  --abstr_cl_out                          false
% 3.98/1.03  
% 3.98/1.03  ------ Global Options
% 3.98/1.03  
% 3.98/1.03  --schedule                              default
% 3.98/1.03  --add_important_lit                     false
% 3.98/1.03  --prop_solver_per_cl                    1000
% 3.98/1.03  --min_unsat_core                        false
% 3.98/1.03  --soft_assumptions                      false
% 3.98/1.03  --soft_lemma_size                       3
% 3.98/1.03  --prop_impl_unit_size                   0
% 3.98/1.03  --prop_impl_unit                        []
% 3.98/1.03  --share_sel_clauses                     true
% 3.98/1.03  --reset_solvers                         false
% 3.98/1.03  --bc_imp_inh                            [conj_cone]
% 3.98/1.03  --conj_cone_tolerance                   3.
% 3.98/1.03  --extra_neg_conj                        none
% 3.98/1.03  --large_theory_mode                     true
% 3.98/1.03  --prolific_symb_bound                   200
% 3.98/1.03  --lt_threshold                          2000
% 3.98/1.03  --clause_weak_htbl                      true
% 3.98/1.03  --gc_record_bc_elim                     false
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing Options
% 3.98/1.03  
% 3.98/1.03  --preprocessing_flag                    true
% 3.98/1.03  --time_out_prep_mult                    0.1
% 3.98/1.03  --splitting_mode                        input
% 3.98/1.03  --splitting_grd                         true
% 3.98/1.03  --splitting_cvd                         false
% 3.98/1.03  --splitting_cvd_svl                     false
% 3.98/1.03  --splitting_nvd                         32
% 3.98/1.03  --sub_typing                            true
% 3.98/1.03  --prep_gs_sim                           true
% 3.98/1.03  --prep_unflatten                        true
% 3.98/1.03  --prep_res_sim                          true
% 3.98/1.03  --prep_upred                            true
% 3.98/1.03  --prep_sem_filter                       exhaustive
% 3.98/1.03  --prep_sem_filter_out                   false
% 3.98/1.03  --pred_elim                             true
% 3.98/1.03  --res_sim_input                         true
% 3.98/1.03  --eq_ax_congr_red                       true
% 3.98/1.03  --pure_diseq_elim                       true
% 3.98/1.03  --brand_transform                       false
% 3.98/1.03  --non_eq_to_eq                          false
% 3.98/1.03  --prep_def_merge                        true
% 3.98/1.03  --prep_def_merge_prop_impl              false
% 3.98/1.03  --prep_def_merge_mbd                    true
% 3.98/1.03  --prep_def_merge_tr_red                 false
% 3.98/1.03  --prep_def_merge_tr_cl                  false
% 3.98/1.03  --smt_preprocessing                     true
% 3.98/1.03  --smt_ac_axioms                         fast
% 3.98/1.03  --preprocessed_out                      false
% 3.98/1.03  --preprocessed_stats                    false
% 3.98/1.03  
% 3.98/1.03  ------ Abstraction refinement Options
% 3.98/1.03  
% 3.98/1.03  --abstr_ref                             []
% 3.98/1.03  --abstr_ref_prep                        false
% 3.98/1.03  --abstr_ref_until_sat                   false
% 3.98/1.03  --abstr_ref_sig_restrict                funpre
% 3.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/1.03  --abstr_ref_under                       []
% 3.98/1.03  
% 3.98/1.03  ------ SAT Options
% 3.98/1.03  
% 3.98/1.03  --sat_mode                              false
% 3.98/1.03  --sat_fm_restart_options                ""
% 3.98/1.03  --sat_gr_def                            false
% 3.98/1.03  --sat_epr_types                         true
% 3.98/1.03  --sat_non_cyclic_types                  false
% 3.98/1.03  --sat_finite_models                     false
% 3.98/1.03  --sat_fm_lemmas                         false
% 3.98/1.03  --sat_fm_prep                           false
% 3.98/1.03  --sat_fm_uc_incr                        true
% 3.98/1.03  --sat_out_model                         small
% 3.98/1.03  --sat_out_clauses                       false
% 3.98/1.03  
% 3.98/1.03  ------ QBF Options
% 3.98/1.03  
% 3.98/1.03  --qbf_mode                              false
% 3.98/1.03  --qbf_elim_univ                         false
% 3.98/1.03  --qbf_dom_inst                          none
% 3.98/1.03  --qbf_dom_pre_inst                      false
% 3.98/1.03  --qbf_sk_in                             false
% 3.98/1.03  --qbf_pred_elim                         true
% 3.98/1.03  --qbf_split                             512
% 3.98/1.03  
% 3.98/1.03  ------ BMC1 Options
% 3.98/1.03  
% 3.98/1.03  --bmc1_incremental                      false
% 3.98/1.03  --bmc1_axioms                           reachable_all
% 3.98/1.03  --bmc1_min_bound                        0
% 3.98/1.03  --bmc1_max_bound                        -1
% 3.98/1.03  --bmc1_max_bound_default                -1
% 3.98/1.03  --bmc1_symbol_reachability              true
% 3.98/1.03  --bmc1_property_lemmas                  false
% 3.98/1.03  --bmc1_k_induction                      false
% 3.98/1.03  --bmc1_non_equiv_states                 false
% 3.98/1.03  --bmc1_deadlock                         false
% 3.98/1.03  --bmc1_ucm                              false
% 3.98/1.03  --bmc1_add_unsat_core                   none
% 3.98/1.03  --bmc1_unsat_core_children              false
% 3.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/1.03  --bmc1_out_stat                         full
% 3.98/1.03  --bmc1_ground_init                      false
% 3.98/1.03  --bmc1_pre_inst_next_state              false
% 3.98/1.03  --bmc1_pre_inst_state                   false
% 3.98/1.03  --bmc1_pre_inst_reach_state             false
% 3.98/1.03  --bmc1_out_unsat_core                   false
% 3.98/1.03  --bmc1_aig_witness_out                  false
% 3.98/1.03  --bmc1_verbose                          false
% 3.98/1.03  --bmc1_dump_clauses_tptp                false
% 3.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.98/1.03  --bmc1_dump_file                        -
% 3.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.98/1.03  --bmc1_ucm_extend_mode                  1
% 3.98/1.03  --bmc1_ucm_init_mode                    2
% 3.98/1.03  --bmc1_ucm_cone_mode                    none
% 3.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.98/1.03  --bmc1_ucm_relax_model                  4
% 3.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/1.03  --bmc1_ucm_layered_model                none
% 3.98/1.03  --bmc1_ucm_max_lemma_size               10
% 3.98/1.03  
% 3.98/1.03  ------ AIG Options
% 3.98/1.03  
% 3.98/1.03  --aig_mode                              false
% 3.98/1.03  
% 3.98/1.03  ------ Instantiation Options
% 3.98/1.03  
% 3.98/1.03  --instantiation_flag                    true
% 3.98/1.03  --inst_sos_flag                         true
% 3.98/1.03  --inst_sos_phase                        true
% 3.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/1.03  --inst_lit_sel_side                     num_symb
% 3.98/1.03  --inst_solver_per_active                1400
% 3.98/1.03  --inst_solver_calls_frac                1.
% 3.98/1.03  --inst_passive_queue_type               priority_queues
% 3.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/1.03  --inst_passive_queues_freq              [25;2]
% 3.98/1.03  --inst_dismatching                      true
% 3.98/1.03  --inst_eager_unprocessed_to_passive     true
% 3.98/1.03  --inst_prop_sim_given                   true
% 3.98/1.03  --inst_prop_sim_new                     false
% 3.98/1.03  --inst_subs_new                         false
% 3.98/1.03  --inst_eq_res_simp                      false
% 3.98/1.03  --inst_subs_given                       false
% 3.98/1.03  --inst_orphan_elimination               true
% 3.98/1.03  --inst_learning_loop_flag               true
% 3.98/1.03  --inst_learning_start                   3000
% 3.98/1.03  --inst_learning_factor                  2
% 3.98/1.03  --inst_start_prop_sim_after_learn       3
% 3.98/1.03  --inst_sel_renew                        solver
% 3.98/1.03  --inst_lit_activity_flag                true
% 3.98/1.03  --inst_restr_to_given                   false
% 3.98/1.03  --inst_activity_threshold               500
% 3.98/1.03  --inst_out_proof                        true
% 3.98/1.03  
% 3.98/1.03  ------ Resolution Options
% 3.98/1.03  
% 3.98/1.03  --resolution_flag                       true
% 3.98/1.03  --res_lit_sel                           adaptive
% 3.98/1.03  --res_lit_sel_side                      none
% 3.98/1.03  --res_ordering                          kbo
% 3.98/1.03  --res_to_prop_solver                    active
% 3.98/1.03  --res_prop_simpl_new                    false
% 3.98/1.03  --res_prop_simpl_given                  true
% 3.98/1.03  --res_passive_queue_type                priority_queues
% 3.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/1.03  --res_passive_queues_freq               [15;5]
% 3.98/1.03  --res_forward_subs                      full
% 3.98/1.03  --res_backward_subs                     full
% 3.98/1.03  --res_forward_subs_resolution           true
% 3.98/1.03  --res_backward_subs_resolution          true
% 3.98/1.03  --res_orphan_elimination                true
% 3.98/1.03  --res_time_limit                        2.
% 3.98/1.03  --res_out_proof                         true
% 3.98/1.03  
% 3.98/1.03  ------ Superposition Options
% 3.98/1.03  
% 3.98/1.03  --superposition_flag                    true
% 3.98/1.03  --sup_passive_queue_type                priority_queues
% 3.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.98/1.03  --demod_completeness_check              fast
% 3.98/1.03  --demod_use_ground                      true
% 3.98/1.03  --sup_to_prop_solver                    passive
% 3.98/1.03  --sup_prop_simpl_new                    true
% 3.98/1.03  --sup_prop_simpl_given                  true
% 3.98/1.03  --sup_fun_splitting                     true
% 3.98/1.03  --sup_smt_interval                      50000
% 3.98/1.03  
% 3.98/1.03  ------ Superposition Simplification Setup
% 3.98/1.03  
% 3.98/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.98/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.98/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.98/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.98/1.03  --sup_immed_triv                        [TrivRules]
% 3.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_immed_bw_main                     []
% 3.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_input_bw                          []
% 3.98/1.03  
% 3.98/1.03  ------ Combination Options
% 3.98/1.03  
% 3.98/1.03  --comb_res_mult                         3
% 3.98/1.03  --comb_sup_mult                         2
% 3.98/1.03  --comb_inst_mult                        10
% 3.98/1.03  
% 3.98/1.03  ------ Debug Options
% 3.98/1.03  
% 3.98/1.03  --dbg_backtrace                         false
% 3.98/1.03  --dbg_dump_prop_clauses                 false
% 3.98/1.03  --dbg_dump_prop_clauses_file            -
% 3.98/1.03  --dbg_out_stat                          false
% 3.98/1.03  ------ Parsing...
% 3.98/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/1.03  ------ Proving...
% 3.98/1.03  ------ Problem Properties 
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  clauses                                 27
% 3.98/1.03  conjectures                             7
% 3.98/1.03  EPR                                     5
% 3.98/1.03  Horn                                    24
% 3.98/1.03  unary                                   9
% 3.98/1.03  binary                                  6
% 3.98/1.03  lits                                    66
% 3.98/1.03  lits eq                                 24
% 3.98/1.03  fd_pure                                 0
% 3.98/1.03  fd_pseudo                               0
% 3.98/1.03  fd_cond                                 0
% 3.98/1.03  fd_pseudo_cond                          1
% 3.98/1.03  AC symbols                              0
% 3.98/1.03  
% 3.98/1.03  ------ Schedule dynamic 5 is on 
% 3.98/1.03  
% 3.98/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  ------ 
% 3.98/1.03  Current options:
% 3.98/1.03  ------ 
% 3.98/1.03  
% 3.98/1.03  ------ Input Options
% 3.98/1.03  
% 3.98/1.03  --out_options                           all
% 3.98/1.03  --tptp_safe_out                         true
% 3.98/1.03  --problem_path                          ""
% 3.98/1.03  --include_path                          ""
% 3.98/1.03  --clausifier                            res/vclausify_rel
% 3.98/1.03  --clausifier_options                    ""
% 3.98/1.03  --stdin                                 false
% 3.98/1.03  --stats_out                             all
% 3.98/1.03  
% 3.98/1.03  ------ General Options
% 3.98/1.03  
% 3.98/1.03  --fof                                   false
% 3.98/1.03  --time_out_real                         305.
% 3.98/1.03  --time_out_virtual                      -1.
% 3.98/1.03  --symbol_type_check                     false
% 3.98/1.03  --clausify_out                          false
% 3.98/1.03  --sig_cnt_out                           false
% 3.98/1.03  --trig_cnt_out                          false
% 3.98/1.03  --trig_cnt_out_tolerance                1.
% 3.98/1.03  --trig_cnt_out_sk_spl                   false
% 3.98/1.03  --abstr_cl_out                          false
% 3.98/1.03  
% 3.98/1.03  ------ Global Options
% 3.98/1.03  
% 3.98/1.03  --schedule                              default
% 3.98/1.03  --add_important_lit                     false
% 3.98/1.03  --prop_solver_per_cl                    1000
% 3.98/1.03  --min_unsat_core                        false
% 3.98/1.03  --soft_assumptions                      false
% 3.98/1.03  --soft_lemma_size                       3
% 3.98/1.03  --prop_impl_unit_size                   0
% 3.98/1.03  --prop_impl_unit                        []
% 3.98/1.03  --share_sel_clauses                     true
% 3.98/1.03  --reset_solvers                         false
% 3.98/1.03  --bc_imp_inh                            [conj_cone]
% 3.98/1.03  --conj_cone_tolerance                   3.
% 3.98/1.03  --extra_neg_conj                        none
% 3.98/1.03  --large_theory_mode                     true
% 3.98/1.03  --prolific_symb_bound                   200
% 3.98/1.03  --lt_threshold                          2000
% 3.98/1.03  --clause_weak_htbl                      true
% 3.98/1.03  --gc_record_bc_elim                     false
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing Options
% 3.98/1.03  
% 3.98/1.03  --preprocessing_flag                    true
% 3.98/1.03  --time_out_prep_mult                    0.1
% 3.98/1.03  --splitting_mode                        input
% 3.98/1.03  --splitting_grd                         true
% 3.98/1.03  --splitting_cvd                         false
% 3.98/1.03  --splitting_cvd_svl                     false
% 3.98/1.03  --splitting_nvd                         32
% 3.98/1.03  --sub_typing                            true
% 3.98/1.03  --prep_gs_sim                           true
% 3.98/1.03  --prep_unflatten                        true
% 3.98/1.03  --prep_res_sim                          true
% 3.98/1.03  --prep_upred                            true
% 3.98/1.03  --prep_sem_filter                       exhaustive
% 3.98/1.03  --prep_sem_filter_out                   false
% 3.98/1.03  --pred_elim                             true
% 3.98/1.03  --res_sim_input                         true
% 3.98/1.03  --eq_ax_congr_red                       true
% 3.98/1.03  --pure_diseq_elim                       true
% 3.98/1.03  --brand_transform                       false
% 3.98/1.03  --non_eq_to_eq                          false
% 3.98/1.03  --prep_def_merge                        true
% 3.98/1.03  --prep_def_merge_prop_impl              false
% 3.98/1.03  --prep_def_merge_mbd                    true
% 3.98/1.03  --prep_def_merge_tr_red                 false
% 3.98/1.03  --prep_def_merge_tr_cl                  false
% 3.98/1.03  --smt_preprocessing                     true
% 3.98/1.03  --smt_ac_axioms                         fast
% 3.98/1.03  --preprocessed_out                      false
% 3.98/1.03  --preprocessed_stats                    false
% 3.98/1.03  
% 3.98/1.03  ------ Abstraction refinement Options
% 3.98/1.03  
% 3.98/1.03  --abstr_ref                             []
% 3.98/1.03  --abstr_ref_prep                        false
% 3.98/1.03  --abstr_ref_until_sat                   false
% 3.98/1.03  --abstr_ref_sig_restrict                funpre
% 3.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/1.03  --abstr_ref_under                       []
% 3.98/1.03  
% 3.98/1.03  ------ SAT Options
% 3.98/1.03  
% 3.98/1.03  --sat_mode                              false
% 3.98/1.03  --sat_fm_restart_options                ""
% 3.98/1.03  --sat_gr_def                            false
% 3.98/1.03  --sat_epr_types                         true
% 3.98/1.03  --sat_non_cyclic_types                  false
% 3.98/1.03  --sat_finite_models                     false
% 3.98/1.03  --sat_fm_lemmas                         false
% 3.98/1.03  --sat_fm_prep                           false
% 3.98/1.03  --sat_fm_uc_incr                        true
% 3.98/1.03  --sat_out_model                         small
% 3.98/1.03  --sat_out_clauses                       false
% 3.98/1.03  
% 3.98/1.03  ------ QBF Options
% 3.98/1.03  
% 3.98/1.03  --qbf_mode                              false
% 3.98/1.03  --qbf_elim_univ                         false
% 3.98/1.03  --qbf_dom_inst                          none
% 3.98/1.03  --qbf_dom_pre_inst                      false
% 3.98/1.03  --qbf_sk_in                             false
% 3.98/1.03  --qbf_pred_elim                         true
% 3.98/1.03  --qbf_split                             512
% 3.98/1.03  
% 3.98/1.03  ------ BMC1 Options
% 3.98/1.03  
% 3.98/1.03  --bmc1_incremental                      false
% 3.98/1.03  --bmc1_axioms                           reachable_all
% 3.98/1.03  --bmc1_min_bound                        0
% 3.98/1.03  --bmc1_max_bound                        -1
% 3.98/1.03  --bmc1_max_bound_default                -1
% 3.98/1.03  --bmc1_symbol_reachability              true
% 3.98/1.03  --bmc1_property_lemmas                  false
% 3.98/1.03  --bmc1_k_induction                      false
% 3.98/1.03  --bmc1_non_equiv_states                 false
% 3.98/1.03  --bmc1_deadlock                         false
% 3.98/1.03  --bmc1_ucm                              false
% 3.98/1.03  --bmc1_add_unsat_core                   none
% 3.98/1.03  --bmc1_unsat_core_children              false
% 3.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/1.03  --bmc1_out_stat                         full
% 3.98/1.03  --bmc1_ground_init                      false
% 3.98/1.03  --bmc1_pre_inst_next_state              false
% 3.98/1.03  --bmc1_pre_inst_state                   false
% 3.98/1.03  --bmc1_pre_inst_reach_state             false
% 3.98/1.03  --bmc1_out_unsat_core                   false
% 3.98/1.03  --bmc1_aig_witness_out                  false
% 3.98/1.03  --bmc1_verbose                          false
% 3.98/1.03  --bmc1_dump_clauses_tptp                false
% 3.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.98/1.03  --bmc1_dump_file                        -
% 3.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.98/1.03  --bmc1_ucm_extend_mode                  1
% 3.98/1.03  --bmc1_ucm_init_mode                    2
% 3.98/1.03  --bmc1_ucm_cone_mode                    none
% 3.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.98/1.03  --bmc1_ucm_relax_model                  4
% 3.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/1.03  --bmc1_ucm_layered_model                none
% 3.98/1.03  --bmc1_ucm_max_lemma_size               10
% 3.98/1.03  
% 3.98/1.03  ------ AIG Options
% 3.98/1.03  
% 3.98/1.03  --aig_mode                              false
% 3.98/1.03  
% 3.98/1.03  ------ Instantiation Options
% 3.98/1.03  
% 3.98/1.03  --instantiation_flag                    true
% 3.98/1.03  --inst_sos_flag                         true
% 3.98/1.03  --inst_sos_phase                        true
% 3.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/1.03  --inst_lit_sel_side                     none
% 3.98/1.03  --inst_solver_per_active                1400
% 3.98/1.03  --inst_solver_calls_frac                1.
% 3.98/1.03  --inst_passive_queue_type               priority_queues
% 3.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/1.03  --inst_passive_queues_freq              [25;2]
% 3.98/1.03  --inst_dismatching                      true
% 3.98/1.03  --inst_eager_unprocessed_to_passive     true
% 3.98/1.03  --inst_prop_sim_given                   true
% 3.98/1.03  --inst_prop_sim_new                     false
% 3.98/1.03  --inst_subs_new                         false
% 3.98/1.03  --inst_eq_res_simp                      false
% 3.98/1.03  --inst_subs_given                       false
% 3.98/1.03  --inst_orphan_elimination               true
% 3.98/1.03  --inst_learning_loop_flag               true
% 3.98/1.03  --inst_learning_start                   3000
% 3.98/1.03  --inst_learning_factor                  2
% 3.98/1.03  --inst_start_prop_sim_after_learn       3
% 3.98/1.03  --inst_sel_renew                        solver
% 3.98/1.03  --inst_lit_activity_flag                true
% 3.98/1.03  --inst_restr_to_given                   false
% 3.98/1.03  --inst_activity_threshold               500
% 3.98/1.03  --inst_out_proof                        true
% 3.98/1.03  
% 3.98/1.03  ------ Resolution Options
% 3.98/1.03  
% 3.98/1.03  --resolution_flag                       false
% 3.98/1.03  --res_lit_sel                           adaptive
% 3.98/1.03  --res_lit_sel_side                      none
% 3.98/1.03  --res_ordering                          kbo
% 3.98/1.03  --res_to_prop_solver                    active
% 3.98/1.03  --res_prop_simpl_new                    false
% 3.98/1.03  --res_prop_simpl_given                  true
% 3.98/1.03  --res_passive_queue_type                priority_queues
% 3.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/1.03  --res_passive_queues_freq               [15;5]
% 3.98/1.03  --res_forward_subs                      full
% 3.98/1.03  --res_backward_subs                     full
% 3.98/1.03  --res_forward_subs_resolution           true
% 3.98/1.03  --res_backward_subs_resolution          true
% 3.98/1.03  --res_orphan_elimination                true
% 3.98/1.03  --res_time_limit                        2.
% 3.98/1.03  --res_out_proof                         true
% 3.98/1.03  
% 3.98/1.03  ------ Superposition Options
% 3.98/1.03  
% 3.98/1.03  --superposition_flag                    true
% 3.98/1.03  --sup_passive_queue_type                priority_queues
% 3.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.98/1.03  --demod_completeness_check              fast
% 3.98/1.03  --demod_use_ground                      true
% 3.98/1.03  --sup_to_prop_solver                    passive
% 3.98/1.03  --sup_prop_simpl_new                    true
% 3.98/1.03  --sup_prop_simpl_given                  true
% 3.98/1.03  --sup_fun_splitting                     true
% 3.98/1.03  --sup_smt_interval                      50000
% 3.98/1.03  
% 3.98/1.03  ------ Superposition Simplification Setup
% 3.98/1.03  
% 3.98/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.98/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.98/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.98/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.98/1.03  --sup_immed_triv                        [TrivRules]
% 3.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_immed_bw_main                     []
% 3.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.03  --sup_input_bw                          []
% 3.98/1.03  
% 3.98/1.03  ------ Combination Options
% 3.98/1.03  
% 3.98/1.03  --comb_res_mult                         3
% 3.98/1.03  --comb_sup_mult                         2
% 3.98/1.03  --comb_inst_mult                        10
% 3.98/1.03  
% 3.98/1.03  ------ Debug Options
% 3.98/1.03  
% 3.98/1.03  --dbg_backtrace                         false
% 3.98/1.03  --dbg_dump_prop_clauses                 false
% 3.98/1.03  --dbg_dump_prop_clauses_file            -
% 3.98/1.03  --dbg_out_stat                          false
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  ------ Proving...
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  % SZS status Theorem for theBenchmark.p
% 3.98/1.03  
% 3.98/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/1.03  
% 3.98/1.03  fof(f15,conjecture,(
% 3.98/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f16,negated_conjecture,(
% 3.98/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.98/1.03    inference(negated_conjecture,[],[f15])).
% 3.98/1.03  
% 3.98/1.03  fof(f36,plain,(
% 3.98/1.03    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.98/1.03    inference(ennf_transformation,[],[f16])).
% 3.98/1.03  
% 3.98/1.03  fof(f37,plain,(
% 3.98/1.03    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.98/1.03    inference(flattening,[],[f36])).
% 3.98/1.03  
% 3.98/1.03  fof(f43,plain,(
% 3.98/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.98/1.03    introduced(choice_axiom,[])).
% 3.98/1.03  
% 3.98/1.03  fof(f42,plain,(
% 3.98/1.03    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.98/1.03    introduced(choice_axiom,[])).
% 3.98/1.03  
% 3.98/1.03  fof(f44,plain,(
% 3.98/1.03    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f43,f42])).
% 3.98/1.03  
% 3.98/1.03  fof(f71,plain,(
% 3.98/1.03    v1_funct_1(sK4)),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f1,axiom,(
% 3.98/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f38,plain,(
% 3.98/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/1.03    inference(nnf_transformation,[],[f1])).
% 3.98/1.03  
% 3.98/1.03  fof(f39,plain,(
% 3.98/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/1.03    inference(flattening,[],[f38])).
% 3.98/1.03  
% 3.98/1.03  fof(f46,plain,(
% 3.98/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.98/1.03    inference(cnf_transformation,[],[f39])).
% 3.98/1.03  
% 3.98/1.03  fof(f78,plain,(
% 3.98/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.98/1.03    inference(equality_resolution,[],[f46])).
% 3.98/1.03  
% 3.98/1.03  fof(f6,axiom,(
% 3.98/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f22,plain,(
% 3.98/1.03    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.98/1.03    inference(ennf_transformation,[],[f6])).
% 3.98/1.03  
% 3.98/1.03  fof(f23,plain,(
% 3.98/1.03    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.98/1.03    inference(flattening,[],[f22])).
% 3.98/1.03  
% 3.98/1.03  fof(f53,plain,(
% 3.98/1.03    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f23])).
% 3.98/1.03  
% 3.98/1.03  fof(f73,plain,(
% 3.98/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f8,axiom,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f26,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(ennf_transformation,[],[f8])).
% 3.98/1.03  
% 3.98/1.03  fof(f55,plain,(
% 3.98/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.03    inference(cnf_transformation,[],[f26])).
% 3.98/1.03  
% 3.98/1.03  fof(f4,axiom,(
% 3.98/1.03    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f20,plain,(
% 3.98/1.03    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.03    inference(ennf_transformation,[],[f4])).
% 3.98/1.03  
% 3.98/1.03  fof(f51,plain,(
% 3.98/1.03    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f20])).
% 3.98/1.03  
% 3.98/1.03  fof(f10,axiom,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f28,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(ennf_transformation,[],[f10])).
% 3.98/1.03  
% 3.98/1.03  fof(f57,plain,(
% 3.98/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.03    inference(cnf_transformation,[],[f28])).
% 3.98/1.03  
% 3.98/1.03  fof(f12,axiom,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f30,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(ennf_transformation,[],[f12])).
% 3.98/1.03  
% 3.98/1.03  fof(f31,plain,(
% 3.98/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(flattening,[],[f30])).
% 3.98/1.03  
% 3.98/1.03  fof(f41,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(nnf_transformation,[],[f31])).
% 3.98/1.03  
% 3.98/1.03  fof(f59,plain,(
% 3.98/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.03    inference(cnf_transformation,[],[f41])).
% 3.98/1.03  
% 3.98/1.03  fof(f72,plain,(
% 3.98/1.03    v1_funct_2(sK4,sK1,sK2)),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f76,plain,(
% 3.98/1.03    k1_xboole_0 != sK2),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f7,axiom,(
% 3.98/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f24,plain,(
% 3.98/1.03    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.98/1.03    inference(ennf_transformation,[],[f7])).
% 3.98/1.03  
% 3.98/1.03  fof(f25,plain,(
% 3.98/1.03    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.03    inference(flattening,[],[f24])).
% 3.98/1.03  
% 3.98/1.03  fof(f54,plain,(
% 3.98/1.03    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f25])).
% 3.98/1.03  
% 3.98/1.03  fof(f75,plain,(
% 3.98/1.03    v2_funct_1(sK4)),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f70,plain,(
% 3.98/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f13,axiom,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f32,plain,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.98/1.03    inference(ennf_transformation,[],[f13])).
% 3.98/1.03  
% 3.98/1.03  fof(f33,plain,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.98/1.03    inference(flattening,[],[f32])).
% 3.98/1.03  
% 3.98/1.03  fof(f66,plain,(
% 3.98/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f33])).
% 3.98/1.03  
% 3.98/1.03  fof(f11,axiom,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f29,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(ennf_transformation,[],[f11])).
% 3.98/1.03  
% 3.98/1.03  fof(f58,plain,(
% 3.98/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.03    inference(cnf_transformation,[],[f29])).
% 3.98/1.03  
% 3.98/1.03  fof(f14,axiom,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f34,plain,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.98/1.03    inference(ennf_transformation,[],[f14])).
% 3.98/1.03  
% 3.98/1.03  fof(f35,plain,(
% 3.98/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.98/1.03    inference(flattening,[],[f34])).
% 3.98/1.03  
% 3.98/1.03  fof(f67,plain,(
% 3.98/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f35])).
% 3.98/1.03  
% 3.98/1.03  fof(f68,plain,(
% 3.98/1.03    v1_funct_1(sK3)),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f74,plain,(
% 3.98/1.03    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  fof(f5,axiom,(
% 3.98/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f21,plain,(
% 3.98/1.03    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.98/1.03    inference(ennf_transformation,[],[f5])).
% 3.98/1.03  
% 3.98/1.03  fof(f52,plain,(
% 3.98/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f21])).
% 3.98/1.03  
% 3.98/1.03  fof(f2,axiom,(
% 3.98/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f18,plain,(
% 3.98/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.98/1.03    inference(ennf_transformation,[],[f2])).
% 3.98/1.03  
% 3.98/1.03  fof(f40,plain,(
% 3.98/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.98/1.03    inference(nnf_transformation,[],[f18])).
% 3.98/1.03  
% 3.98/1.03  fof(f48,plain,(
% 3.98/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f40])).
% 3.98/1.03  
% 3.98/1.03  fof(f9,axiom,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f17,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.98/1.03    inference(pure_predicate_removal,[],[f9])).
% 3.98/1.03  
% 3.98/1.03  fof(f27,plain,(
% 3.98/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.03    inference(ennf_transformation,[],[f17])).
% 3.98/1.03  
% 3.98/1.03  fof(f56,plain,(
% 3.98/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.03    inference(cnf_transformation,[],[f27])).
% 3.98/1.03  
% 3.98/1.03  fof(f47,plain,(
% 3.98/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f39])).
% 3.98/1.03  
% 3.98/1.03  fof(f3,axiom,(
% 3.98/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.03  
% 3.98/1.03  fof(f19,plain,(
% 3.98/1.03    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.98/1.03    inference(ennf_transformation,[],[f3])).
% 3.98/1.03  
% 3.98/1.03  fof(f50,plain,(
% 3.98/1.03    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.98/1.03    inference(cnf_transformation,[],[f19])).
% 3.98/1.03  
% 3.98/1.03  fof(f77,plain,(
% 3.98/1.03    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.98/1.03    inference(cnf_transformation,[],[f44])).
% 3.98/1.03  
% 3.98/1.03  cnf(c_29,negated_conjecture,
% 3.98/1.03      ( v1_funct_1(sK4) ),
% 3.98/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1043,plain,
% 3.98/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1,plain,
% 3.98/1.03      ( r1_tarski(X0,X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1055,plain,
% 3.98/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_8,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.98/1.03      | ~ v1_funct_1(X1)
% 3.98/1.03      | ~ v1_relat_1(X1)
% 3.98/1.03      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.98/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1051,plain,
% 3.98/1.03      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.98/1.03      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.98/1.03      | v1_funct_1(X0) != iProver_top
% 3.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2387,plain,
% 3.98/1.03      ( k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) = k2_relat_1(X0)
% 3.98/1.03      | v1_funct_1(X0) != iProver_top
% 3.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1055,c_1051]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3417,plain,
% 3.98/1.03      ( k9_relat_1(sK4,k10_relat_1(sK4,k2_relat_1(sK4))) = k2_relat_1(sK4)
% 3.98/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1043,c_2387]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_27,negated_conjecture,
% 3.98/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.98/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1044,plain,
% 3.98/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_10,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | v1_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1050,plain,
% 3.98/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1387,plain,
% 3.98/1.03      ( v1_relat_1(sK4) = iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1044,c_1050]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_6,plain,
% 3.98/1.03      ( ~ v1_relat_1(X0)
% 3.98/1.03      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1053,plain,
% 3.98/1.03      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1447,plain,
% 3.98/1.03      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1387,c_1053]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_12,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1049,plain,
% 3.98/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1839,plain,
% 3.98/1.03      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1044,c_1049]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_19,plain,
% 3.98/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.98/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.98/1.03      | k1_xboole_0 = X2 ),
% 3.98/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_28,negated_conjecture,
% 3.98/1.03      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.98/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_455,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.98/1.03      | sK4 != X0
% 3.98/1.03      | sK2 != X2
% 3.98/1.03      | sK1 != X1
% 3.98/1.03      | k1_xboole_0 = X2 ),
% 3.98/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_456,plain,
% 3.98/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.98/1.03      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.98/1.03      | k1_xboole_0 = sK2 ),
% 3.98/1.03      inference(unflattening,[status(thm)],[c_455]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_24,negated_conjecture,
% 3.98/1.03      ( k1_xboole_0 != sK2 ),
% 3.98/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_458,plain,
% 3.98/1.03      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_456,c_27,c_24]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1841,plain,
% 3.98/1.03      ( k1_relat_1(sK4) = sK1 ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_1839,c_458]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2255,plain,
% 3.98/1.03      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_1447,c_1447,c_1841]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3422,plain,
% 3.98/1.03      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4)
% 3.98/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_3417,c_2255]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_38,plain,
% 3.98/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1113,plain,
% 3.98/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/1.03      | v1_relat_1(sK4) ),
% 3.98/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1167,plain,
% 3.98/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.98/1.03      | v1_relat_1(sK4) ),
% 3.98/1.03      inference(instantiation,[status(thm)],[c_1113]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1168,plain,
% 3.98/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.98/1.03      | v1_relat_1(sK4) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3853,plain,
% 3.98/1.03      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_3422,c_38,c_1168]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_9,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.98/1.03      | ~ v2_funct_1(X1)
% 3.98/1.03      | ~ v1_funct_1(X1)
% 3.98/1.03      | ~ v1_relat_1(X1)
% 3.98/1.03      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.98/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_25,negated_conjecture,
% 3.98/1.03      ( v2_funct_1(sK4) ),
% 3.98/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_334,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.98/1.03      | ~ v1_funct_1(X1)
% 3.98/1.03      | ~ v1_relat_1(X1)
% 3.98/1.03      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
% 3.98/1.03      | sK4 != X1 ),
% 3.98/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_335,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.98/1.03      | ~ v1_funct_1(sK4)
% 3.98/1.03      | ~ v1_relat_1(sK4)
% 3.98/1.03      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 3.98/1.03      inference(unflattening,[status(thm)],[c_334]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_339,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.98/1.03      | ~ v1_relat_1(sK4)
% 3.98/1.03      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_335,c_29]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1040,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 3.98/1.03      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.98/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_341,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 3.98/1.03      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.98/1.03      | v1_relat_1(sK4) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1740,plain,
% 3.98/1.03      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.98/1.03      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_1040,c_38,c_341,c_1168]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1741,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 3.98/1.03      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.98/1.03      inference(renaming,[status(thm)],[c_1740]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1746,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1055,c_1741]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2294,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,sK1)) = sK1 ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_1746,c_1746,c_1841]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3855,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = sK1 ),
% 3.98/1.03      inference(demodulation,[status(thm)],[c_3853,c_2294]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_30,negated_conjecture,
% 3.98/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.98/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1042,plain,
% 3.98/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_20,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.98/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.98/1.03      | ~ v1_funct_1(X0)
% 3.98/1.03      | ~ v1_funct_1(X3) ),
% 3.98/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1047,plain,
% 3.98/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.98/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.98/1.03      | v1_funct_1(X0) != iProver_top
% 3.98/1.03      | v1_funct_1(X3) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_13,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1048,plain,
% 3.98/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2510,plain,
% 3.98/1.03      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 3.98/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.98/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.98/1.03      | v1_funct_1(X5) != iProver_top
% 3.98/1.03      | v1_funct_1(X4) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1047,c_1048]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5401,plain,
% 3.98/1.03      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | v1_funct_1(X2) != iProver_top
% 3.98/1.03      | v1_funct_1(sK4) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1044,c_2510]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_36,plain,
% 3.98/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5751,plain,
% 3.98/1.03      ( v1_funct_1(X2) != iProver_top
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_5401,c_36]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5752,plain,
% 3.98/1.03      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.98/1.03      inference(renaming,[status(thm)],[c_5751]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5759,plain,
% 3.98/1.03      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 3.98/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1042,c_5752]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_22,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.98/1.03      | ~ v1_funct_1(X0)
% 3.98/1.03      | ~ v1_funct_1(X3)
% 3.98/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1045,plain,
% 3.98/1.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.98/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.98/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | v1_funct_1(X5) != iProver_top
% 3.98/1.03      | v1_funct_1(X4) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2458,plain,
% 3.98/1.03      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | v1_funct_1(X2) != iProver_top
% 3.98/1.03      | v1_funct_1(sK4) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1044,c_1045]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2575,plain,
% 3.98/1.03      ( v1_funct_1(X2) != iProver_top
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_2458,c_36]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2576,plain,
% 3.98/1.03      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.98/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.98/1.03      inference(renaming,[status(thm)],[c_2575]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2583,plain,
% 3.98/1.03      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.98/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1042,c_2576]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_32,negated_conjecture,
% 3.98/1.03      ( v1_funct_1(sK3) ),
% 3.98/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_33,plain,
% 3.98/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2657,plain,
% 3.98/1.03      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_2583,c_33]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_26,negated_conjecture,
% 3.98/1.03      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.98/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2659,plain,
% 3.98/1.03      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.98/1.03      inference(demodulation,[status(thm)],[c_2657,c_26]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5764,plain,
% 3.98/1.03      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 3.98/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_5759,c_2657,c_2659]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5871,plain,
% 3.98/1.03      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_5764,c_33]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_7,plain,
% 3.98/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.98/1.03      | ~ v1_relat_1(X1)
% 3.98/1.03      | ~ v1_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1052,plain,
% 3.98/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.98/1.03      | v1_relat_1(X0) != iProver_top
% 3.98/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5879,plain,
% 3.98/1.03      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 3.98/1.03      | v1_relat_1(sK4) != iProver_top
% 3.98/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_5871,c_1052]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_35,plain,
% 3.98/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1354,plain,
% 3.98/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.98/1.03      | v1_relat_1(sK3) ),
% 3.98/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1355,plain,
% 3.98/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.98/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_1354]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_6193,plain,
% 3.98/1.03      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_5879,c_35,c_38,c_1168,c_1355]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_4,plain,
% 3.98/1.03      ( ~ v5_relat_1(X0,X1)
% 3.98/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 3.98/1.03      | ~ v1_relat_1(X0) ),
% 3.98/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_11,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | v5_relat_1(X0,X2) ),
% 3.98/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_360,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | r1_tarski(k2_relat_1(X3),X4)
% 3.98/1.03      | ~ v1_relat_1(X3)
% 3.98/1.03      | X0 != X3
% 3.98/1.03      | X2 != X4 ),
% 3.98/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_11]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_361,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 3.98/1.03      | ~ v1_relat_1(X0) ),
% 3.98/1.03      inference(unflattening,[status(thm)],[c_360]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_365,plain,
% 3.98/1.03      ( r1_tarski(k2_relat_1(X0),X2)
% 3.98/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.98/1.03      inference(global_propositional_subsumption,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_361,c_10]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_366,plain,
% 3.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.03      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.98/1.03      inference(renaming,[status(thm)],[c_365]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1039,plain,
% 3.98/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2382,plain,
% 3.98/1.03      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1044,c_1039]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_0,plain,
% 3.98/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.98/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1056,plain,
% 3.98/1.03      ( X0 = X1
% 3.98/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.98/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2530,plain,
% 3.98/1.03      ( k2_relat_1(sK4) = sK2
% 3.98/1.03      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_2382,c_1056]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_6199,plain,
% 3.98/1.03      ( k2_relat_1(sK4) = sK2 ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_6193,c_2530]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2383,plain,
% 3.98/1.03      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1042,c_1039]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2013,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 3.98/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 3.98/1.03      inference(demodulation,[status(thm)],[c_1841,c_1741]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3253,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_2383,c_2013]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1388,plain,
% 3.98/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1042,c_1050]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_5,plain,
% 3.98/1.03      ( ~ v1_relat_1(X0)
% 3.98/1.03      | ~ v1_relat_1(X1)
% 3.98/1.03      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 3.98/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1054,plain,
% 3.98/1.03      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 3.98/1.03      | v1_relat_1(X0) != iProver_top
% 3.98/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.98/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1894,plain,
% 3.98/1.03      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 3.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1387,c_1054]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_2297,plain,
% 3.98/1.03      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1388,c_1894]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_3254,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_3253,c_2297]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_8795,plain,
% 3.98/1.03      ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(sK3) ),
% 3.98/1.03      inference(light_normalisation,[status(thm)],[c_3254,c_3254,c_5871]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_13054,plain,
% 3.98/1.03      ( k2_relat_1(sK3) = sK1 ),
% 3.98/1.03      inference(light_normalisation,
% 3.98/1.03                [status(thm)],
% 3.98/1.03                [c_3855,c_3855,c_6199,c_8795]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1445,plain,
% 3.98/1.03      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.98/1.03      inference(superposition,[status(thm)],[c_1042,c_1048]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_23,negated_conjecture,
% 3.98/1.03      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.98/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(c_1604,plain,
% 3.98/1.03      ( k2_relat_1(sK3) != sK1 ),
% 3.98/1.03      inference(demodulation,[status(thm)],[c_1445,c_23]) ).
% 3.98/1.03  
% 3.98/1.03  cnf(contradiction,plain,
% 3.98/1.03      ( $false ),
% 3.98/1.03      inference(minisat,[status(thm)],[c_13054,c_1604]) ).
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/1.03  
% 3.98/1.03  ------                               Statistics
% 3.98/1.03  
% 3.98/1.03  ------ General
% 3.98/1.03  
% 3.98/1.03  abstr_ref_over_cycles:                  0
% 3.98/1.03  abstr_ref_under_cycles:                 0
% 3.98/1.03  gc_basic_clause_elim:                   0
% 3.98/1.03  forced_gc_time:                         0
% 3.98/1.03  parsing_time:                           0.011
% 3.98/1.03  unif_index_cands_time:                  0.
% 3.98/1.03  unif_index_add_time:                    0.
% 3.98/1.03  orderings_time:                         0.
% 3.98/1.03  out_proof_time:                         0.012
% 3.98/1.03  total_time:                             0.505
% 3.98/1.03  num_of_symbols:                         55
% 3.98/1.03  num_of_terms:                           11519
% 3.98/1.03  
% 3.98/1.03  ------ Preprocessing
% 3.98/1.03  
% 3.98/1.03  num_of_splits:                          0
% 3.98/1.03  num_of_split_atoms:                     0
% 3.98/1.03  num_of_reused_defs:                     0
% 3.98/1.03  num_eq_ax_congr_red:                    16
% 3.98/1.03  num_of_sem_filtered_clauses:            1
% 3.98/1.03  num_of_subtypes:                        0
% 3.98/1.03  monotx_restored_types:                  0
% 3.98/1.03  sat_num_of_epr_types:                   0
% 3.98/1.03  sat_num_of_non_cyclic_types:            0
% 3.98/1.03  sat_guarded_non_collapsed_types:        0
% 3.98/1.03  num_pure_diseq_elim:                    0
% 3.98/1.03  simp_replaced_by:                       0
% 3.98/1.03  res_preprocessed:                       146
% 3.98/1.03  prep_upred:                             0
% 3.98/1.03  prep_unflattend:                        37
% 3.98/1.03  smt_new_axioms:                         0
% 3.98/1.03  pred_elim_cands:                        4
% 3.98/1.03  pred_elim:                              3
% 3.98/1.03  pred_elim_cl:                           5
% 3.98/1.03  pred_elim_cycles:                       5
% 3.98/1.03  merged_defs:                            0
% 3.98/1.03  merged_defs_ncl:                        0
% 3.98/1.03  bin_hyper_res:                          0
% 3.98/1.03  prep_cycles:                            4
% 3.98/1.03  pred_elim_time:                         0.004
% 3.98/1.03  splitting_time:                         0.
% 3.98/1.03  sem_filter_time:                        0.
% 3.98/1.03  monotx_time:                            0.
% 3.98/1.03  subtype_inf_time:                       0.
% 3.98/1.03  
% 3.98/1.03  ------ Problem properties
% 3.98/1.03  
% 3.98/1.03  clauses:                                27
% 3.98/1.03  conjectures:                            7
% 3.98/1.03  epr:                                    5
% 3.98/1.03  horn:                                   24
% 3.98/1.03  ground:                                 13
% 3.98/1.03  unary:                                  9
% 3.98/1.03  binary:                                 6
% 3.98/1.03  lits:                                   66
% 3.98/1.03  lits_eq:                                24
% 3.98/1.03  fd_pure:                                0
% 3.98/1.03  fd_pseudo:                              0
% 3.98/1.03  fd_cond:                                0
% 3.98/1.03  fd_pseudo_cond:                         1
% 3.98/1.03  ac_symbols:                             0
% 3.98/1.03  
% 3.98/1.03  ------ Propositional Solver
% 3.98/1.03  
% 3.98/1.03  prop_solver_calls:                      33
% 3.98/1.03  prop_fast_solver_calls:                 1488
% 3.98/1.03  smt_solver_calls:                       0
% 3.98/1.03  smt_fast_solver_calls:                  0
% 3.98/1.03  prop_num_of_clauses:                    6614
% 3.98/1.03  prop_preprocess_simplified:             10210
% 3.98/1.03  prop_fo_subsumed:                       184
% 3.98/1.03  prop_solver_time:                       0.
% 3.98/1.03  smt_solver_time:                        0.
% 3.98/1.03  smt_fast_solver_time:                   0.
% 3.98/1.03  prop_fast_solver_time:                  0.
% 3.98/1.03  prop_unsat_core_time:                   0.
% 3.98/1.03  
% 3.98/1.03  ------ QBF
% 3.98/1.03  
% 3.98/1.03  qbf_q_res:                              0
% 3.98/1.03  qbf_num_tautologies:                    0
% 3.98/1.03  qbf_prep_cycles:                        0
% 3.98/1.03  
% 3.98/1.03  ------ BMC1
% 3.98/1.03  
% 3.98/1.03  bmc1_current_bound:                     -1
% 3.98/1.03  bmc1_last_solved_bound:                 -1
% 3.98/1.03  bmc1_unsat_core_size:                   -1
% 3.98/1.03  bmc1_unsat_core_parents_size:           -1
% 3.98/1.03  bmc1_merge_next_fun:                    0
% 3.98/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.98/1.03  
% 3.98/1.03  ------ Instantiation
% 3.98/1.03  
% 3.98/1.03  inst_num_of_clauses:                    1914
% 3.98/1.03  inst_num_in_passive:                    522
% 3.98/1.03  inst_num_in_active:                     1113
% 3.98/1.03  inst_num_in_unprocessed:                279
% 3.98/1.03  inst_num_of_loops:                      1210
% 3.98/1.03  inst_num_of_learning_restarts:          0
% 3.98/1.03  inst_num_moves_active_passive:          90
% 3.98/1.03  inst_lit_activity:                      0
% 3.98/1.03  inst_lit_activity_moves:                0
% 3.98/1.03  inst_num_tautologies:                   0
% 3.98/1.03  inst_num_prop_implied:                  0
% 3.98/1.03  inst_num_existing_simplified:           0
% 3.98/1.03  inst_num_eq_res_simplified:             0
% 3.98/1.03  inst_num_child_elim:                    0
% 3.98/1.03  inst_num_of_dismatching_blockings:      708
% 3.98/1.03  inst_num_of_non_proper_insts:           2653
% 3.98/1.03  inst_num_of_duplicates:                 0
% 3.98/1.03  inst_inst_num_from_inst_to_res:         0
% 3.98/1.03  inst_dismatching_checking_time:         0.
% 3.98/1.03  
% 3.98/1.03  ------ Resolution
% 3.98/1.03  
% 3.98/1.03  res_num_of_clauses:                     0
% 3.98/1.03  res_num_in_passive:                     0
% 3.98/1.03  res_num_in_active:                      0
% 3.98/1.03  res_num_of_loops:                       150
% 3.98/1.03  res_forward_subset_subsumed:            239
% 3.98/1.03  res_backward_subset_subsumed:           0
% 3.98/1.03  res_forward_subsumed:                   0
% 3.98/1.03  res_backward_subsumed:                  0
% 3.98/1.03  res_forward_subsumption_resolution:     0
% 3.98/1.03  res_backward_subsumption_resolution:    0
% 3.98/1.03  res_clause_to_clause_subsumption:       1067
% 3.98/1.03  res_orphan_elimination:                 0
% 3.98/1.03  res_tautology_del:                      219
% 3.98/1.03  res_num_eq_res_simplified:              0
% 3.98/1.03  res_num_sel_changes:                    0
% 3.98/1.03  res_moves_from_active_to_pass:          0
% 3.98/1.03  
% 3.98/1.03  ------ Superposition
% 3.98/1.03  
% 3.98/1.03  sup_time_total:                         0.
% 3.98/1.03  sup_time_generating:                    0.
% 3.98/1.03  sup_time_sim_full:                      0.
% 3.98/1.03  sup_time_sim_immed:                     0.
% 3.98/1.03  
% 3.98/1.03  sup_num_of_clauses:                     519
% 3.98/1.03  sup_num_in_active:                      228
% 3.98/1.03  sup_num_in_passive:                     291
% 3.98/1.03  sup_num_of_loops:                       240
% 3.98/1.03  sup_fw_superposition:                   217
% 3.98/1.03  sup_bw_superposition:                   338
% 3.98/1.03  sup_immediate_simplified:               121
% 3.98/1.03  sup_given_eliminated:                   1
% 3.98/1.03  comparisons_done:                       0
% 3.98/1.03  comparisons_avoided:                    3
% 3.98/1.03  
% 3.98/1.03  ------ Simplifications
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  sim_fw_subset_subsumed:                 7
% 3.98/1.03  sim_bw_subset_subsumed:                 25
% 3.98/1.03  sim_fw_subsumed:                        4
% 3.98/1.03  sim_bw_subsumed:                        0
% 3.98/1.03  sim_fw_subsumption_res:                 0
% 3.98/1.03  sim_bw_subsumption_res:                 0
% 3.98/1.03  sim_tautology_del:                      0
% 3.98/1.03  sim_eq_tautology_del:                   11
% 3.98/1.03  sim_eq_res_simp:                        0
% 3.98/1.03  sim_fw_demodulated:                     13
% 3.98/1.03  sim_bw_demodulated:                     7
% 3.98/1.03  sim_light_normalised:                   124
% 3.98/1.03  sim_joinable_taut:                      0
% 3.98/1.03  sim_joinable_simp:                      0
% 3.98/1.03  sim_ac_normalised:                      0
% 3.98/1.03  sim_smt_subsumption:                    0
% 3.98/1.03  
%------------------------------------------------------------------------------
