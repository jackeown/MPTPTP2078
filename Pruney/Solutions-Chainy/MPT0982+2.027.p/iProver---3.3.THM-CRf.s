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
% DateTime   : Thu Dec  3 12:01:42 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 614 expanded)
%              Number of clauses        :   84 ( 183 expanded)
%              Number of leaves         :   15 ( 153 expanded)
%              Depth                    :   16
%              Number of atoms          :  477 (4329 expanded)
%              Number of equality atoms :  214 (1450 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f31,f37,f36])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1253,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1255,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3633,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1255])).

cnf(c_3993,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1251,c_3633])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4225,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_1258])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5755,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4225,c_32,c_35])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1256,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5766,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5755,c_1256])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1254,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3685,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1254])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4912,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3685,c_33])).

cnf(c_4913,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4912])).

cnf(c_4925,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_4913])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1700,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_2125,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3327,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_5012,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4925,c_29,c_27,c_26,c_24,c_3327])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5017,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5012,c_23])).

cnf(c_5788,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5766,c_5017])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1257,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2301,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1253,c_1257])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_465,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_467,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_24,c_21])).

cnf(c_2306,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2301,c_467])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_357,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_358,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( ~ v1_funct_1(X0)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_26])).

cnf(c_363,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_1249,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_364,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1437,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1438,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1437])).

cnf(c_2135,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1249,c_35,c_364,c_1438])).

cnf(c_2136,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2135])).

cnf(c_2814,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2306,c_2136])).

cnf(c_5828,plain,
    ( k2_relat_1(sK4) != sK2
    | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5788,c_2814])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1261,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5826,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5788,c_1261])).

cnf(c_2285,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1251,c_1256])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2852,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2285,c_1259])).

cnf(c_5171,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2852,c_32])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5176,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5171,c_1262])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1265,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5226,plain,
    ( k2_relat_1(sK3) = sK1
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5176,c_1265])).

cnf(c_2284,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1253,c_1256])).

cnf(c_2848,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_1259])).

cnf(c_5159,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2848,c_35])).

cnf(c_5164,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_1262])).

cnf(c_5222,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5164,c_1265])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2851,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_2285,c_20])).

cnf(c_1440,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1441,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1440])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5828,c_5826,c_5226,c_5222,c_2851,c_1441,c_1438,c_35,c_32,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       true
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 26
% 3.18/1.00  conjectures                             7
% 3.18/1.00  EPR                                     5
% 3.18/1.00  Horn                                    23
% 3.18/1.00  unary                                   9
% 3.18/1.00  binary                                  7
% 3.18/1.00  lits                                    59
% 3.18/1.00  lits eq                                 22
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 0
% 3.18/1.00  fd_pseudo_cond                          1
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Schedule dynamic 5 is on 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     none
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       false
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f13,conjecture,(
% 3.18/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f14,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.18/1.00    inference(negated_conjecture,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.18/1.00    inference(ennf_transformation,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f31,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.18/1.00    inference(flattening,[],[f30])).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f38,plain,(
% 3.18/1.00    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f31,f37,f36])).
% 3.18/1.00  
% 3.18/1.00  fof(f61,plain,(
% 3.18/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f64,plain,(
% 3.18/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f10,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.18/1.00    inference(ennf_transformation,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f24])).
% 3.18/1.00  
% 3.18/1.00  fof(f51,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f25])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f20,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.18/1.00    inference(ennf_transformation,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f20])).
% 3.18/1.00  
% 3.18/1.00  fof(f48,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f21])).
% 3.18/1.00  
% 3.18/1.00  fof(f9,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f50,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f23])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/1.00    inference(ennf_transformation,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/1.00    inference(flattening,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f58,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f62,plain,(
% 3.18/1.00    v1_funct_1(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f59,plain,(
% 3.18/1.00    v1_funct_1(sK3)),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f65,plain,(
% 3.18/1.00    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f22])).
% 3.18/1.00  
% 3.18/1.00  fof(f11,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f26])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(nnf_transformation,[],[f27])).
% 3.18/1.00  
% 3.18/1.00  fof(f52,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f35])).
% 3.18/1.00  
% 3.18/1.00  fof(f63,plain,(
% 3.18/1.00    v1_funct_2(sK4,sK1,sK2)),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f67,plain,(
% 3.18/1.00    k1_xboole_0 != sK2),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/1.00    inference(flattening,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f45,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f66,plain,(
% 3.18/1.00    v2_funct_1(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.18/1.00    inference(ennf_transformation,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f47,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.18/1.00    inference(nnf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f42,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f1,axiom,(
% 3.18/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/1.00    inference(nnf_transformation,[],[f1])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/1.00    inference(flattening,[],[f32])).
% 3.18/1.00  
% 3.18/1.00  fof(f41,plain,(
% 3.18/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f33])).
% 3.18/1.00  
% 3.18/1.00  fof(f68,plain,(
% 3.18/1.00    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.18/1.00    inference(cnf_transformation,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_27,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1251,plain,
% 3.18/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_24,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1253,plain,
% 3.18/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/1.00      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1255,plain,
% 3.18/1.00      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.18/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.18/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3633,plain,
% 3.18/1.00      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1253,c_1255]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3993,plain,
% 3.18/1.00      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1251,c_3633]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/1.00      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1258,plain,
% 3.18/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.18/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.18/1.00      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4225,plain,
% 3.18/1.00      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.18/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.18/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3993,c_1258]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_32,plain,
% 3.18/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_35,plain,
% 3.18/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5755,plain,
% 3.18/1.00      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4225,c_32,c_35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1256,plain,
% 3.18/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5766,plain,
% 3.18/1.00      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5755,c_1256]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_funct_1(X3)
% 3.18/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1254,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.18/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.18/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X5) != iProver_top
% 3.18/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3685,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top
% 3.18/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1253,c_1254]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_26,negated_conjecture,
% 3.18/1.00      ( v1_funct_1(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_33,plain,
% 3.18/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4912,plain,
% 3.18/1.00      ( v1_funct_1(X2) != iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3685,c_33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4913,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_4912]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4925,plain,
% 3.18/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.18/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1251,c_4913]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_29,negated_conjecture,
% 3.18/1.00      ( v1_funct_1(sK3) ),
% 3.18/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1527,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_funct_1(sK4)
% 3.18/1.00      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1700,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.18/1.00      | ~ v1_funct_1(sK4)
% 3.18/1.00      | ~ v1_funct_1(sK3)
% 3.18/1.00      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1527]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2125,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.18/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/1.00      | ~ v1_funct_1(sK4)
% 3.18/1.00      | ~ v1_funct_1(sK3)
% 3.18/1.00      | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1700]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3327,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.18/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.18/1.00      | ~ v1_funct_1(sK4)
% 3.18/1.00      | ~ v1_funct_1(sK3)
% 3.18/1.00      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2125]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5012,plain,
% 3.18/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4925,c_29,c_27,c_26,c_24,c_3327]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_23,negated_conjecture,
% 3.18/1.00      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5017,plain,
% 3.18/1.00      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_5012,c_23]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5788,plain,
% 3.18/1.00      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_5766,c_5017]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1257,plain,
% 3.18/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2301,plain,
% 3.18/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1253,c_1257]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_18,plain,
% 3.18/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.18/1.00      | k1_xboole_0 = X2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_25,negated_conjecture,
% 3.18/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_464,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.18/1.00      | sK4 != X0
% 3.18/1.00      | sK2 != X2
% 3.18/1.00      | sK1 != X1
% 3.18/1.00      | k1_xboole_0 = X2 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_465,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.18/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.18/1.00      | k1_xboole_0 = sK2 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_464]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_21,negated_conjecture,
% 3.18/1.00      ( k1_xboole_0 != sK2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_467,plain,
% 3.18/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_465,c_24,c_21]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2306,plain,
% 3.18/1.00      ( k1_relat_1(sK4) = sK1 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_2301,c_467]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.18/1.00      | ~ v1_funct_1(X1)
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v2_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X1)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_22,negated_conjecture,
% 3.18/1.00      ( v2_funct_1(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_357,plain,
% 3.18/1.00      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.18/1.00      | ~ v1_funct_1(X1)
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X1)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
% 3.18/1.00      | sK4 != X0 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_358,plain,
% 3.18/1.00      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_funct_1(sK4)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | ~ v1_relat_1(sK4)
% 3.18/1.00      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_362,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0)
% 3.18/1.00      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | ~ v1_relat_1(sK4)
% 3.18/1.00      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_358,c_26]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_363,plain,
% 3.18/1.00      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | ~ v1_relat_1(sK4)
% 3.18/1.00      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_362]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1249,plain,
% 3.18/1.00      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.18/1.00      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_364,plain,
% 3.18/1.00      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.18/1.00      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | v1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1437,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.18/1.00      | v1_relat_1(sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1438,plain,
% 3.18/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.18/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1437]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2135,plain,
% 3.18/1.00      ( v1_relat_1(X0) != iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 3.18/1.00      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_1249,c_35,c_364,c_1438]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2136,plain,
% 3.18/1.00      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.18/1.00      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_2135]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2814,plain,
% 3.18/1.00      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.18/1.00      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_2306,c_2136]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5828,plain,
% 3.18/1.00      ( k2_relat_1(sK4) != sK2
% 3.18/1.00      | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK3) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5788,c_2814]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5,plain,
% 3.18/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.18/1.00      | ~ v1_relat_1(X1)
% 3.18/1.00      | ~ v1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1261,plain,
% 3.18/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5826,plain,
% 3.18/1.00      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 3.18/1.00      | v1_relat_1(sK4) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5788,c_1261]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2285,plain,
% 3.18/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1251,c_1256]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1259,plain,
% 3.18/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.18/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2852,plain,
% 3.18/1.00      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 3.18/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2285,c_1259]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5171,plain,
% 3.18/1.00      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2852,c_32]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1262,plain,
% 3.18/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5176,plain,
% 3.18/1.00      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5171,c_1262]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1265,plain,
% 3.18/1.00      ( X0 = X1
% 3.18/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.18/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5226,plain,
% 3.18/1.00      ( k2_relat_1(sK3) = sK1
% 3.18/1.00      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5176,c_1265]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2284,plain,
% 3.18/1.00      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1253,c_1256]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2848,plain,
% 3.18/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 3.18/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2284,c_1259]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5159,plain,
% 3.18/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2848,c_35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5164,plain,
% 3.18/1.00      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5159,c_1262]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5222,plain,
% 3.18/1.00      ( k2_relat_1(sK4) = sK2
% 3.18/1.00      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5164,c_1265]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_20,negated_conjecture,
% 3.18/1.00      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2851,plain,
% 3.18/1.00      ( k2_relat_1(sK3) != sK1 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_2285,c_20]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1440,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.18/1.00      | v1_relat_1(sK3) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1441,plain,
% 3.18/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1440]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_30,plain,
% 3.18/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_5828,c_5826,c_5226,c_5222,c_2851,c_1441,c_1438,c_35,
% 3.18/1.00                 c_32,c_30]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.02
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.01
% 3.18/1.00  total_time:                             0.194
% 3.18/1.00  num_of_symbols:                         52
% 3.18/1.00  num_of_terms:                           5842
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    26
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       136
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        35
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        4
% 3.18/1.00  pred_elim:                              2
% 3.18/1.00  pred_elim_cl:                           3
% 3.18/1.00  pred_elim_cycles:                       4
% 3.18/1.00  merged_defs:                            8
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          8
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.004
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                26
% 3.18/1.00  conjectures:                            7
% 3.18/1.00  epr:                                    5
% 3.18/1.00  horn:                                   23
% 3.18/1.00  ground:                                 13
% 3.18/1.00  unary:                                  9
% 3.18/1.00  binary:                                 7
% 3.18/1.00  lits:                                   59
% 3.18/1.00  lits_eq:                                22
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                0
% 3.18/1.00  fd_pseudo_cond:                         1
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      28
% 3.18/1.00  prop_fast_solver_calls:                 891
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    2314
% 3.18/1.00  prop_preprocess_simplified:             6553
% 3.18/1.00  prop_fo_subsumed:                       21
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    755
% 3.18/1.00  inst_num_in_passive:                    284
% 3.18/1.00  inst_num_in_active:                     426
% 3.18/1.00  inst_num_in_unprocessed:                45
% 3.18/1.00  inst_num_of_loops:                      460
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          32
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                1
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      168
% 3.18/1.00  inst_num_of_non_proper_insts:           473
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       140
% 3.18/1.00  res_forward_subset_subsumed:            15
% 3.18/1.00  res_backward_subset_subsumed:           0
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       354
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      35
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     150
% 3.18/1.00  sup_num_in_active:                      86
% 3.18/1.00  sup_num_in_passive:                     64
% 3.18/1.00  sup_num_of_loops:                       90
% 3.18/1.00  sup_fw_superposition:                   80
% 3.18/1.00  sup_bw_superposition:                   76
% 3.18/1.00  sup_immediate_simplified:               8
% 3.18/1.00  sup_given_eliminated:                   0
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    3
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 0
% 3.18/1.00  sim_bw_subset_subsumed:                 1
% 3.18/1.00  sim_fw_subsumed:                        1
% 3.18/1.00  sim_bw_subsumed:                        0
% 3.18/1.00  sim_fw_subsumption_res:                 0
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      1
% 3.18/1.00  sim_eq_tautology_del:                   1
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     0
% 3.18/1.00  sim_bw_demodulated:                     7
% 3.18/1.00  sim_light_normalised:                   5
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
