%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:01 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  257 (13696 expanded)
%              Number of clauses        :  185 (4880 expanded)
%              Number of leaves         :   19 (2519 expanded)
%              Depth                    :   29
%              Number of atoms          :  731 (71902 expanded)
%              Number of equality atoms :  411 (18794 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f40])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2857,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2866,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3617,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2866])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_230])).

cnf(c_2855,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_6751,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3617,c_2855])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7135,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7136,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7135])).

cnf(c_7175,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6751,c_7136])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2858,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_966,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_30])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2863,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3824,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2857,c_2863])).

cnf(c_3975,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_968,c_3824])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2864,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4202,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_2864])).

cnf(c_4586,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_4202])).

cnf(c_7184,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7175,c_4586])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2859,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7450,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7184,c_2859])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2860,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5011,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2860])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3193,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3791,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_5337,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5011,c_32,c_30,c_3791])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2861,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4280,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2861])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_3355,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3354])).

cnf(c_4425,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_33,c_35,c_3355])).

cnf(c_5346,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5337,c_4425])).

cnf(c_8826,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7450,c_5346])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_976,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_977,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_989,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_977,c_404])).

cnf(c_2844,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_994,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_3257,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_3258,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3257])).

cnf(c_3389,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2844,c_33,c_35,c_994,c_3258])).

cnf(c_3390,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3389])).

cnf(c_5342,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5337,c_3390])).

cnf(c_7452,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7184,c_5342])).

cnf(c_8837,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8826,c_7452])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2862,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5942,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_2862])).

cnf(c_6371,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5942,c_33,c_35])).

cnf(c_6378,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6371,c_2866])).

cnf(c_6753,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6378,c_2855])).

cnf(c_9133,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6753,c_7136])).

cnf(c_2853,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_6382,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6371,c_2853])).

cnf(c_9959,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8837,c_9133,c_6382])).

cnf(c_9982,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9959,c_3617])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9987,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9959,c_28])).

cnf(c_9988,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9987])).

cnf(c_10002,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9982,c_9988])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10004,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10002,c_2])).

cnf(c_6750,plain,
    ( v1_relat_1(sK2) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_2855])).

cnf(c_10214,plain,
    ( v1_relat_1(sK2) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9988,c_6750])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_3117,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_3118,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3117])).

cnf(c_3120,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3118])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3285,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3288,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3285])).

cnf(c_3290,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3288])).

cnf(c_11054,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10214,c_89,c_3120,c_3290])).

cnf(c_2868,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4201,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_2864])).

cnf(c_11059,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11054,c_4201])).

cnf(c_10216,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9988,c_2858])).

cnf(c_2867,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_2854,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_5863,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2854])).

cnf(c_5898,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2867,c_5863])).

cnf(c_10232,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10216,c_5898])).

cnf(c_11201,plain,
    ( k7_relat_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10232,c_89,c_3120,c_3290,c_10214])).

cnf(c_12060,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11059,c_11201])).

cnf(c_12071,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12060,c_2864])).

cnf(c_12075,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12071,c_11201,c_12060])).

cnf(c_12930,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12075,c_89,c_3120,c_3290,c_10214])).

cnf(c_12931,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12930])).

cnf(c_12938,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10004,c_12931])).

cnf(c_5862,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2854])).

cnf(c_7181,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(superposition,[status(thm)],[c_7175,c_5862])).

cnf(c_10213,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_9988,c_7181])).

cnf(c_7180,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7175,c_4201])).

cnf(c_7651,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7180,c_2859])).

cnf(c_7663,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7651,c_2])).

cnf(c_5391,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5346])).

cnf(c_6783,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6753])).

cnf(c_7849,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7663,c_5391,c_6783,c_7136])).

cnf(c_7857,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6382,c_7849])).

cnf(c_9439,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7857,c_6783,c_7136])).

cnf(c_9449,plain,
    ( k7_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) = k7_relat_1(sK3,k1_xboole_0)
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9439,c_5863])).

cnf(c_9902,plain,
    ( k7_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9449,c_6783,c_7136])).

cnf(c_10345,plain,
    ( k7_relat_1(sK3,X0) = sK3 ),
    inference(demodulation,[status(thm)],[c_10213,c_9902])).

cnf(c_9973,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9959,c_6371])).

cnf(c_10039,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9973,c_9988])).

cnf(c_10041,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10039,c_2])).

cnf(c_995,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_995])).

cnf(c_2843,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1568,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_3267,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != sK0
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2843,c_33,c_35,c_1568,c_3258])).

cnf(c_3268,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3267])).

cnf(c_5343,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5337,c_3268])).

cnf(c_9977,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9959,c_5343])).

cnf(c_10016,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9977,c_9988])).

cnf(c_10020,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10016,c_1])).

cnf(c_10043,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10041,c_10020])).

cnf(c_11797,plain,
    ( sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_10345,c_10043])).

cnf(c_11804,plain,
    ( sK2 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11797])).

cnf(c_446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_230])).

cnf(c_447,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_15,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_725,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_447,c_15])).

cnf(c_795,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_725,c_27])).

cnf(c_796,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_2852,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_5344,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5337,c_2852])).

cnf(c_5362,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5344,c_5346])).

cnf(c_2238,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5156,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | k7_relat_1(sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_5157,plain,
    ( k7_relat_1(sK3,sK2) != X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5156])).

cnf(c_5159,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5157])).

cnf(c_8152,plain,
    ( sK2 = k1_xboole_0
    | k7_relat_1(sK3,sK2) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5362,c_89,c_3120,c_3290,c_5159,c_7452])).

cnf(c_8153,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8152])).

cnf(c_9965,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9959,c_8153])).

cnf(c_10088,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9965,c_1])).

cnf(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2236,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2245,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_2237,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3182,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_2237])).

cnf(c_3567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3182])).

cnf(c_7301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(X3))
    | k7_relat_1(sK3,X2) != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3567])).

cnf(c_9400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X2))
    | k7_relat_1(sK3,sK2) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_7301])).

cnf(c_9402,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k7_relat_1(sK3,sK2) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9400])).

cnf(c_10109,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10088])).

cnf(c_11494,plain,
    ( sK2 = k1_xboole_0
    | k7_relat_1(sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10088,c_101,c_103,c_104,c_106,c_2245,c_9402,c_10109])).

cnf(c_11495,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11494])).

cnf(c_11798,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10345,c_11495])).

cnf(c_11807,plain,
    ( sK3 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11804,c_11798])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12938,c_11807])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     num_symb
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       true
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 31
% 3.54/0.98  conjectures                             4
% 3.54/0.98  EPR                                     5
% 3.54/0.98  Horn                                    26
% 3.54/0.98  unary                                   7
% 3.54/0.98  binary                                  5
% 3.54/0.98  lits                                    89
% 3.54/0.98  lits eq                                 34
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 3
% 3.54/0.98  fd_pseudo_cond                          0
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Schedule dynamic 5 is on 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     none
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       false
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f15,conjecture,(
% 3.54/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f16,negated_conjecture,(
% 3.54/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.54/0.98    inference(negated_conjecture,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f33,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.54/0.98    inference(ennf_transformation,[],[f16])).
% 3.54/0.98  
% 3.54/0.98  fof(f34,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.54/0.98    inference(flattening,[],[f33])).
% 3.54/0.98  
% 3.54/0.98  fof(f40,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f41,plain,(
% 3.54/0.98    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f40])).
% 3.54/0.98  
% 3.54/0.98  fof(f71,plain,(
% 3.54/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f37,plain,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.54/0.98    inference(nnf_transformation,[],[f3])).
% 3.54/0.98  
% 3.54/0.98  fof(f46,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f37])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f17,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  fof(f48,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f17])).
% 3.54/0.98  
% 3.54/0.98  fof(f47,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f37])).
% 3.54/0.98  
% 3.54/0.98  fof(f6,axiom,(
% 3.54/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f51,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f6])).
% 3.54/0.98  
% 3.54/0.98  fof(f72,plain,(
% 3.54/0.98    r1_tarski(sK2,sK0)),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f11,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f25,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f11])).
% 3.54/0.98  
% 3.54/0.98  fof(f26,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(flattening,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f39,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(nnf_transformation,[],[f26])).
% 3.54/0.98  
% 3.54/0.98  fof(f57,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f39])).
% 3.54/0.98  
% 3.54/0.98  fof(f70,plain,(
% 3.54/0.98    v1_funct_2(sK3,sK0,sK1)),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f10,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f24,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f10])).
% 3.54/0.98  
% 3.54/0.98  fof(f56,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f8,axiom,(
% 3.54/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f21,plain,(
% 3.54/0.98    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(ennf_transformation,[],[f8])).
% 3.54/0.98  
% 3.54/0.98  fof(f22,plain,(
% 3.54/0.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(flattening,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f53,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f22])).
% 3.54/0.98  
% 3.54/0.98  fof(f14,axiom,(
% 3.54/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f31,plain,(
% 3.54/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.54/0.98    inference(ennf_transformation,[],[f14])).
% 3.54/0.98  
% 3.54/0.98  fof(f32,plain,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(flattening,[],[f31])).
% 3.54/0.98  
% 3.54/0.98  fof(f68,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f13,axiom,(
% 3.54/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f29,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.54/0.98    inference(ennf_transformation,[],[f13])).
% 3.54/0.98  
% 3.54/0.98  fof(f30,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.54/0.98    inference(flattening,[],[f29])).
% 3.54/0.98  
% 3.54/0.98  fof(f65,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f30])).
% 3.54/0.98  
% 3.54/0.98  fof(f69,plain,(
% 3.54/0.98    v1_funct_1(sK3)),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f12,axiom,(
% 3.54/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f27,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.54/0.98    inference(ennf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f28,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.54/0.98    inference(flattening,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  fof(f63,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f28])).
% 3.54/0.98  
% 3.54/0.98  fof(f67,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f74,plain,(
% 3.54/0.98    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f9,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f23,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f9])).
% 3.54/0.98  
% 3.54/0.98  fof(f55,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f5,axiom,(
% 3.54/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f18,plain,(
% 3.54/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(ennf_transformation,[],[f5])).
% 3.54/0.98  
% 3.54/0.98  fof(f38,plain,(
% 3.54/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(nnf_transformation,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f49,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f38])).
% 3.54/0.98  
% 3.54/0.98  fof(f64,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f28])).
% 3.54/0.98  
% 3.54/0.98  fof(f73,plain,(
% 3.54/0.98    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.54/0.98    inference(cnf_transformation,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f2,axiom,(
% 3.54/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f35,plain,(
% 3.54/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.54/0.98    inference(nnf_transformation,[],[f2])).
% 3.54/0.98  
% 3.54/0.98  fof(f36,plain,(
% 3.54/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.54/0.98    inference(flattening,[],[f35])).
% 3.54/0.98  
% 3.54/0.98  fof(f44,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f36])).
% 3.54/0.98  
% 3.54/0.98  fof(f76,plain,(
% 3.54/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.54/0.98    inference(equality_resolution,[],[f44])).
% 3.54/0.98  
% 3.54/0.98  fof(f1,axiom,(
% 3.54/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f42,plain,(
% 3.54/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f1])).
% 3.54/0.98  
% 3.54/0.98  fof(f45,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.54/0.98    inference(cnf_transformation,[],[f36])).
% 3.54/0.98  
% 3.54/0.98  fof(f75,plain,(
% 3.54/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.54/0.98    inference(equality_resolution,[],[f45])).
% 3.54/0.98  
% 3.54/0.98  fof(f54,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f7,axiom,(
% 3.54/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f19,plain,(
% 3.54/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.54/0.98    inference(ennf_transformation,[],[f7])).
% 3.54/0.98  
% 3.54/0.98  fof(f20,plain,(
% 3.54/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(flattening,[],[f19])).
% 3.54/0.98  
% 3.54/0.98  fof(f52,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f20])).
% 3.54/0.98  
% 3.54/0.98  fof(f62,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f39])).
% 3.54/0.98  
% 3.54/0.98  fof(f77,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(equality_resolution,[],[f62])).
% 3.54/0.98  
% 3.54/0.98  fof(f78,plain,(
% 3.54/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.54/0.98    inference(equality_resolution,[],[f77])).
% 3.54/0.98  
% 3.54/0.98  fof(f43,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f36])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_30,negated_conjecture,
% 3.54/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2857,plain,
% 3.54/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2866,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3617,plain,
% 3.54/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2857,c_2866]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.98      | ~ v1_relat_1(X1)
% 3.54/0.98      | v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_229,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.54/0.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_230,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_229]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_288,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.54/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_230]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2855,plain,
% 3.54/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.54/0.98      | v1_relat_1(X1) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6751,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.54/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3617,c_2855]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7135,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7136,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_7135]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7175,plain,
% 3.54/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6751,c_7136]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_29,negated_conjecture,
% 3.54/0.98      ( r1_tarski(sK2,sK0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2858,plain,
% 3.54/0.98      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_20,plain,
% 3.54/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.54/0.98      | k1_xboole_0 = X2 ),
% 3.54/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_31,negated_conjecture,
% 3.54/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_965,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.54/0.98      | sK3 != X0
% 3.54/0.98      | sK1 != X2
% 3.54/0.98      | sK0 != X1
% 3.54/0.98      | k1_xboole_0 = X2 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_966,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.54/0.98      | k1_xboole_0 = sK1 ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_965]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_968,plain,
% 3.54/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_966,c_30]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2863,plain,
% 3.54/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.54/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3824,plain,
% 3.54/0.98      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2857,c_2863]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3975,plain,
% 3.54/0.98      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_968,c_3824]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.54/0.98      | ~ v1_relat_1(X1)
% 3.54/0.98      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2864,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.54/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4202,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.54/0.98      | sK1 = k1_xboole_0
% 3.54/0.98      | r1_tarski(X0,sK0) != iProver_top
% 3.54/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3975,c_2864]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4586,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
% 3.54/0.98      | sK1 = k1_xboole_0
% 3.54/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2858,c_4202]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7184,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7175,c_4586]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_24,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2859,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7450,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0
% 3.54/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7184,c_2859]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_23,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.54/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2860,plain,
% 3.54/0.98      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.54/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.54/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5011,plain,
% 3.54/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.54/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2857,c_2860]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_32,negated_conjecture,
% 3.54/0.98      ( v1_funct_1(sK3) ),
% 3.54/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3193,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/0.98      | ~ v1_funct_1(sK3)
% 3.54/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3791,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | ~ v1_funct_1(sK3)
% 3.54/0.98      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3193]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5337,plain,
% 3.54/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_5011,c_32,c_30,c_3791]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_22,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2861,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4280,plain,
% 3.54/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.54/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2857,c_2861]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_33,plain,
% 3.54/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_35,plain,
% 3.54/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3177,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/0.98      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.54/0.98      | ~ v1_funct_1(sK3) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3354,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.54/0.98      | ~ v1_funct_1(sK3) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3177]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3355,plain,
% 3.54/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.54/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3354]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4425,plain,
% 3.54/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_4280,c_33,c_35,c_3355]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5346,plain,
% 3.54/0.98      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_5337,c_4425]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8826,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0
% 3.54/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(forward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_7450,c_5346]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_25,plain,
% 3.54/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_27,negated_conjecture,
% 3.54/0.98      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.54/0.98      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_976,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.54/0.98      | k1_relat_1(X0) != sK2
% 3.54/0.98      | sK1 != X1 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_977,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.54/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_976]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12,plain,
% 3.54/0.98      ( v5_relat_1(X0,X1)
% 3.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8,plain,
% 3.54/0.98      ( ~ v5_relat_1(X0,X1)
% 3.54/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_404,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_989,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.54/0.98      inference(forward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_977,c_404]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2844,plain,
% 3.54/0.98      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.54/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 3.54/0.98      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_994,plain,
% 3.54/0.98      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.54/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 3.54/0.98      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3257,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.98      | ~ v1_funct_1(sK3) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3177]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3258,plain,
% 3.54/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.54/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3257]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3389,plain,
% 3.54/0.98      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.54/0.98      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_2844,c_33,c_35,c_994,c_3258]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3390,plain,
% 3.54/0.98      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.54/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_3389]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5342,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.54/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_5337,c_3390]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7452,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0
% 3.54/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7184,c_5342]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8837,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_8826,c_7452]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_21,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | ~ v1_funct_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2862,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5942,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.54/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_5337,c_2862]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6371,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_5942,c_33,c_35]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6378,plain,
% 3.54/0.98      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6371,c_2866]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6753,plain,
% 3.54/0.98      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.54/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6378,c_2855]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9133,plain,
% 3.54/0.98      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6753,c_7136]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2853,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6382,plain,
% 3.54/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6371,c_2853]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9959,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0 ),
% 3.54/0.98      inference(forward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_8837,c_9133,c_6382]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9982,plain,
% 3.54/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_9959,c_3617]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_28,negated_conjecture,
% 3.54/0.98      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9987,plain,
% 3.54/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_9959,c_28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9988,plain,
% 3.54/0.98      ( sK0 = k1_xboole_0 ),
% 3.54/0.98      inference(equality_resolution_simp,[status(thm)],[c_9987]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10002,plain,
% 3.54/0.98      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_9982,c_9988]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2,plain,
% 3.54/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10004,plain,
% 3.54/0.98      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_10002,c_2]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6750,plain,
% 3.54/0.98      ( v1_relat_1(sK2) = iProver_top | v1_relat_1(sK0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2858,c_2855]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10214,plain,
% 3.54/0.98      ( v1_relat_1(sK2) = iProver_top
% 3.54/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_9988,c_6750]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_87,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_89,plain,
% 3.54/0.98      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_87]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3117,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.54/0.98      | v1_relat_1(X0)
% 3.54/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_288]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3118,plain,
% 3.54/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) = iProver_top
% 3.54/0.98      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3117]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3120,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.54/0.98      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.54/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3118]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_0,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3285,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3288,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3285]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3290,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3288]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11054,plain,
% 3.54/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_10214,c_89,c_3120,c_3290]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2868,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4201,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2868,c_2864]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11059,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_11054,c_4201]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10216,plain,
% 3.54/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_9988,c_2858]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2867,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.54/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1,plain,
% 3.54/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_13,plain,
% 3.54/0.98      ( v4_relat_1(X0,X1)
% 3.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10,plain,
% 3.54/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_386,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2854,plain,
% 3.54/0.98      ( k7_relat_1(X0,X1) = X0
% 3.54/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5863,plain,
% 3.54/0.98      ( k7_relat_1(X0,X1) = X0
% 3.54/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_1,c_2854]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5898,plain,
% 3.54/0.98      ( k7_relat_1(X0,X1) = X0
% 3.54/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2867,c_5863]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10232,plain,
% 3.54/0.98      ( k7_relat_1(sK2,X0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_10216,c_5898]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11201,plain,
% 3.54/0.98      ( k7_relat_1(sK2,X0) = sK2 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_10232,c_89,c_3120,c_3290,c_10214]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12060,plain,
% 3.54/0.98      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_11059,c_11201]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12071,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
% 3.54/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_12060,c_2864]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12075,plain,
% 3.54/0.98      ( k1_xboole_0 = X0
% 3.54/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_12071,c_11201,c_12060]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12930,plain,
% 3.54/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_12075,c_89,c_3120,c_3290,c_10214]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12931,plain,
% 3.54/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_12930]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12938,plain,
% 3.54/0.98      ( sK3 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_10004,c_12931]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5862,plain,
% 3.54/0.98      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2857,c_2854]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7181,plain,
% 3.54/0.98      ( k7_relat_1(sK3,sK0) = sK3 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7175,c_5862]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10213,plain,
% 3.54/0.98      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_9988,c_7181]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7180,plain,
% 3.54/0.98      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7175,c_4201]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7651,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7180,c_2859]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7663,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_7651,c_2]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5391,plain,
% 3.54/0.98      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_5346]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6783,plain,
% 3.54/0.98      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 3.54/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_6753]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7849,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_7663,c_5391,c_6783,c_7136]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7857,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6382,c_7849]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9439,plain,
% 3.54/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_7857,c_6783,c_7136]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9449,plain,
% 3.54/0.98      ( k7_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) = k7_relat_1(sK3,k1_xboole_0)
% 3.54/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_9439,c_5863]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9902,plain,
% 3.54/0.99      ( k7_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) = k7_relat_1(sK3,k1_xboole_0) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_9449,c_6783,c_7136]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10345,plain,
% 3.54/0.99      ( k7_relat_1(sK3,X0) = sK3 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10213,c_9902]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9973,plain,
% 3.54/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_9959,c_6371]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10039,plain,
% 3.54/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_9973,c_9988]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10041,plain,
% 3.54/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10039,c_2]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_995,plain,
% 3.54/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | sK1 != sK1 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1567,plain,
% 3.54/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0 ),
% 3.54/0.99      inference(equality_resolution_simp,[status(thm)],[c_995]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2843,plain,
% 3.54/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1568,plain,
% 3.54/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3267,plain,
% 3.54/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2843,c_33,c_35,c_1568,c_3258]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3268,plain,
% 3.54/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_3267]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5343,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_5337,c_3268]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9977,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 3.54/0.99      | sK2 != sK0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_9959,c_5343]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10016,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 3.54/0.99      | sK2 != k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_9977,c_9988]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10020,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 3.54/0.99      | sK2 != k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10016,c_1]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10043,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != sK3 | sK2 != k1_xboole_0 ),
% 3.54/0.99      inference(backward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_10041,c_10020]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11797,plain,
% 3.54/0.99      ( sK2 != k1_xboole_0 | sK3 != sK3 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10345,c_10043]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11804,plain,
% 3.54/0.99      ( sK2 != k1_xboole_0 ),
% 3.54/0.99      inference(equality_resolution_simp,[status(thm)],[c_11797]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_446,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_230]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_447,plain,
% 3.54/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_15,plain,
% 3.54/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.54/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.54/0.99      | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_725,plain,
% 3.54/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(backward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_447,c_15]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_795,plain,
% 3.54/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 != X0
% 3.54/0.99      | sK1 != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_725,c_27]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_796,plain,
% 3.54/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.54/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.54/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK1 != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = sK2 ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_795]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2852,plain,
% 3.54/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK1 != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = sK2
% 3.54/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5344,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0
% 3.54/0.99      | sK1 != k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.54/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_5337,c_2852]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5362,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0
% 3.54/0.99      | sK1 != k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.54/0.99      inference(forward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5344,c_5346]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2238,plain,
% 3.54/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.54/0.99      theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5156,plain,
% 3.54/0.99      ( ~ v1_relat_1(X0)
% 3.54/0.99      | v1_relat_1(k7_relat_1(sK3,sK2))
% 3.54/0.99      | k7_relat_1(sK3,sK2) != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2238]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5157,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != X0
% 3.54/0.99      | v1_relat_1(X0) != iProver_top
% 3.54/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_5156]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5159,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 3.54/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_5157]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8152,plain,
% 3.54/0.99      ( sK2 = k1_xboole_0
% 3.54/0.99      | k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5362,c_89,c_3120,c_3290,c_5159,c_7452]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8153,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_8152]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9965,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_9959,c_8153]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10088,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_9965,c_1]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_101,plain,
% 3.54/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.54/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3,plain,
% 3.54/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = X1
% 3.54/0.99      | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_103,plain,
% 3.54/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_104,plain,
% 3.54/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_106,plain,
% 3.54/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2236,plain,
% 3.54/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.54/0.99      theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2245,plain,
% 3.54/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 3.54/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2236]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2237,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.54/0.99      theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3182,plain,
% 3.54/0.99      ( m1_subset_1(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.54/0.99      | X0 != X2
% 3.54/0.99      | X1 != k1_zfmisc_1(X3) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2237]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3567,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.54/0.99      | X2 != X0
% 3.54/0.99      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_3182]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7301,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(X3))
% 3.54/0.99      | k7_relat_1(sK3,X2) != X0
% 3.54/0.99      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_3567]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9400,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X2))
% 3.54/0.99      | k7_relat_1(sK3,sK2) != X0
% 3.54/0.99      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_7301]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9402,plain,
% 3.54/0.99      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
% 3.54/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.54/0.99      | k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_9400]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10109,plain,
% 3.54/0.99      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
% 3.54/0.99      | k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.54/0.99      | sK2 = k1_xboole_0 ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_10088]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11494,plain,
% 3.54/0.99      ( sK2 = k1_xboole_0 | k7_relat_1(sK3,sK2) != k1_xboole_0 ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_10088,c_101,c_103,c_104,c_106,c_2245,c_9402,c_10109]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11495,plain,
% 3.54/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_11494]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11798,plain,
% 3.54/0.99      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10345,c_11495]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11807,plain,
% 3.54/0.99      ( sK3 != k1_xboole_0 ),
% 3.54/0.99      inference(backward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_11804,c_11798]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,[status(thm)],[c_12938,c_11807]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ General
% 3.54/0.99  
% 3.54/0.99  abstr_ref_over_cycles:                  0
% 3.54/0.99  abstr_ref_under_cycles:                 0
% 3.54/0.99  gc_basic_clause_elim:                   0
% 3.54/0.99  forced_gc_time:                         0
% 3.54/0.99  parsing_time:                           0.012
% 3.54/0.99  unif_index_cands_time:                  0.
% 3.54/0.99  unif_index_add_time:                    0.
% 3.54/0.99  orderings_time:                         0.
% 3.54/0.99  out_proof_time:                         0.018
% 3.54/0.99  total_time:                             0.371
% 3.54/0.99  num_of_symbols:                         50
% 3.54/0.99  num_of_terms:                           12534
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing
% 3.54/0.99  
% 3.54/0.99  num_of_splits:                          0
% 3.54/0.99  num_of_split_atoms:                     0
% 3.54/0.99  num_of_reused_defs:                     0
% 3.54/0.99  num_eq_ax_congr_red:                    15
% 3.54/0.99  num_of_sem_filtered_clauses:            1
% 3.54/0.99  num_of_subtypes:                        0
% 3.54/0.99  monotx_restored_types:                  0
% 3.54/0.99  sat_num_of_epr_types:                   0
% 3.54/0.99  sat_num_of_non_cyclic_types:            0
% 3.54/0.99  sat_guarded_non_collapsed_types:        0
% 3.54/0.99  num_pure_diseq_elim:                    0
% 3.54/0.99  simp_replaced_by:                       0
% 3.54/0.99  res_preprocessed:                       148
% 3.54/0.99  prep_upred:                             0
% 3.54/0.99  prep_unflattend:                        138
% 3.54/0.99  smt_new_axioms:                         0
% 3.54/0.99  pred_elim_cands:                        4
% 3.54/0.99  pred_elim:                              3
% 3.54/0.99  pred_elim_cl:                           1
% 3.54/0.99  pred_elim_cycles:                       6
% 3.54/0.99  merged_defs:                            8
% 3.54/0.99  merged_defs_ncl:                        0
% 3.54/0.99  bin_hyper_res:                          9
% 3.54/0.99  prep_cycles:                            4
% 3.54/0.99  pred_elim_time:                         0.03
% 3.54/0.99  splitting_time:                         0.
% 3.54/0.99  sem_filter_time:                        0.
% 3.54/0.99  monotx_time:                            0.001
% 3.54/0.99  subtype_inf_time:                       0.
% 3.54/0.99  
% 3.54/0.99  ------ Problem properties
% 3.54/0.99  
% 3.54/0.99  clauses:                                31
% 3.54/0.99  conjectures:                            4
% 3.54/0.99  epr:                                    5
% 3.54/0.99  horn:                                   26
% 3.54/0.99  ground:                                 12
% 3.54/0.99  unary:                                  7
% 3.54/0.99  binary:                                 5
% 3.54/0.99  lits:                                   89
% 3.54/0.99  lits_eq:                                34
% 3.54/0.99  fd_pure:                                0
% 3.54/0.99  fd_pseudo:                              0
% 3.54/0.99  fd_cond:                                3
% 3.54/0.99  fd_pseudo_cond:                         0
% 3.54/0.99  ac_symbols:                             0
% 3.54/0.99  
% 3.54/0.99  ------ Propositional Solver
% 3.54/0.99  
% 3.54/0.99  prop_solver_calls:                      30
% 3.54/0.99  prop_fast_solver_calls:                 1597
% 3.54/0.99  smt_solver_calls:                       0
% 3.54/0.99  smt_fast_solver_calls:                  0
% 3.54/0.99  prop_num_of_clauses:                    4700
% 3.54/0.99  prop_preprocess_simplified:             9431
% 3.54/0.99  prop_fo_subsumed:                       40
% 3.54/0.99  prop_solver_time:                       0.
% 3.54/0.99  smt_solver_time:                        0.
% 3.54/0.99  smt_fast_solver_time:                   0.
% 3.54/0.99  prop_fast_solver_time:                  0.
% 3.54/0.99  prop_unsat_core_time:                   0.
% 3.54/0.99  
% 3.54/0.99  ------ QBF
% 3.54/0.99  
% 3.54/0.99  qbf_q_res:                              0
% 3.54/0.99  qbf_num_tautologies:                    0
% 3.54/0.99  qbf_prep_cycles:                        0
% 3.54/0.99  
% 3.54/0.99  ------ BMC1
% 3.54/0.99  
% 3.54/0.99  bmc1_current_bound:                     -1
% 3.54/0.99  bmc1_last_solved_bound:                 -1
% 3.54/0.99  bmc1_unsat_core_size:                   -1
% 3.54/0.99  bmc1_unsat_core_parents_size:           -1
% 3.54/0.99  bmc1_merge_next_fun:                    0
% 3.54/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation
% 3.54/0.99  
% 3.54/0.99  inst_num_of_clauses:                    1361
% 3.54/0.99  inst_num_in_passive:                    16
% 3.54/0.99  inst_num_in_active:                     701
% 3.54/0.99  inst_num_in_unprocessed:                644
% 3.54/0.99  inst_num_of_loops:                      780
% 3.54/0.99  inst_num_of_learning_restarts:          0
% 3.54/0.99  inst_num_moves_active_passive:          75
% 3.54/0.99  inst_lit_activity:                      0
% 3.54/0.99  inst_lit_activity_moves:                0
% 3.54/0.99  inst_num_tautologies:                   0
% 3.54/0.99  inst_num_prop_implied:                  0
% 3.54/0.99  inst_num_existing_simplified:           0
% 3.54/0.99  inst_num_eq_res_simplified:             0
% 3.54/0.99  inst_num_child_elim:                    0
% 3.54/0.99  inst_num_of_dismatching_blockings:      566
% 3.54/0.99  inst_num_of_non_proper_insts:           1528
% 3.54/0.99  inst_num_of_duplicates:                 0
% 3.54/0.99  inst_inst_num_from_inst_to_res:         0
% 3.54/0.99  inst_dismatching_checking_time:         0.
% 3.54/0.99  
% 3.54/0.99  ------ Resolution
% 3.54/0.99  
% 3.54/0.99  res_num_of_clauses:                     0
% 3.54/0.99  res_num_in_passive:                     0
% 3.54/0.99  res_num_in_active:                      0
% 3.54/0.99  res_num_of_loops:                       152
% 3.54/0.99  res_forward_subset_subsumed:            28
% 3.54/0.99  res_backward_subset_subsumed:           2
% 3.54/0.99  res_forward_subsumed:                   0
% 3.54/0.99  res_backward_subsumed:                  0
% 3.54/0.99  res_forward_subsumption_resolution:     3
% 3.54/0.99  res_backward_subsumption_resolution:    1
% 3.54/0.99  res_clause_to_clause_subsumption:       660
% 3.54/0.99  res_orphan_elimination:                 0
% 3.54/0.99  res_tautology_del:                      140
% 3.54/0.99  res_num_eq_res_simplified:              1
% 3.54/0.99  res_num_sel_changes:                    0
% 3.54/0.99  res_moves_from_active_to_pass:          0
% 3.54/0.99  
% 3.54/0.99  ------ Superposition
% 3.54/0.99  
% 3.54/0.99  sup_time_total:                         0.
% 3.54/0.99  sup_time_generating:                    0.
% 3.54/0.99  sup_time_sim_full:                      0.
% 3.54/0.99  sup_time_sim_immed:                     0.
% 3.54/0.99  
% 3.54/0.99  sup_num_of_clauses:                     165
% 3.54/0.99  sup_num_in_active:                      73
% 3.54/0.99  sup_num_in_passive:                     92
% 3.54/0.99  sup_num_of_loops:                       155
% 3.54/0.99  sup_fw_superposition:                   119
% 3.54/0.99  sup_bw_superposition:                   209
% 3.54/0.99  sup_immediate_simplified:               120
% 3.54/0.99  sup_given_eliminated:                   1
% 3.54/0.99  comparisons_done:                       0
% 3.54/0.99  comparisons_avoided:                    28
% 3.54/0.99  
% 3.54/0.99  ------ Simplifications
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  sim_fw_subset_subsumed:                 31
% 3.54/0.99  sim_bw_subset_subsumed:                 21
% 3.54/0.99  sim_fw_subsumed:                        16
% 3.54/0.99  sim_bw_subsumed:                        10
% 3.54/0.99  sim_fw_subsumption_res:                 8
% 3.54/0.99  sim_bw_subsumption_res:                 4
% 3.54/0.99  sim_tautology_del:                      11
% 3.54/0.99  sim_eq_tautology_del:                   24
% 3.54/0.99  sim_eq_res_simp:                        4
% 3.54/0.99  sim_fw_demodulated:                     23
% 3.54/0.99  sim_bw_demodulated:                     69
% 3.54/0.99  sim_light_normalised:                   44
% 3.54/0.99  sim_joinable_taut:                      0
% 3.54/0.99  sim_joinable_simp:                      0
% 3.54/0.99  sim_ac_normalised:                      0
% 3.54/0.99  sim_smt_subsumption:                    0
% 3.54/0.99  
%------------------------------------------------------------------------------
