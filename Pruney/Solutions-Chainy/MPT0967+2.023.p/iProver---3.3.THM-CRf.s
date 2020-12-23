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
% DateTime   : Thu Dec  3 12:00:42 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  223 (1638 expanded)
%              Number of clauses        :  152 ( 689 expanded)
%              Number of leaves         :   24 ( 310 expanded)
%              Depth                    :   22
%              Number of atoms          :  639 (7308 expanded)
%              Number of equality atoms :  353 (2209 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f44])).

fof(f75,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_539,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_31])).

cnf(c_1361,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1364,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2836,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1361,c_1364])).

cnf(c_3141,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_539,c_2836])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_13])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_2162,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1359])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_15])).

cnf(c_1358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_1742,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1358])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1362,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1372,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3099,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_1372])).

cnf(c_3208,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_3099])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2305,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1367])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_242])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_243])).

cnf(c_1360,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_2680,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_1360])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2963,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2964,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_3361,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3208,c_2680,c_2964])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2835,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1364])).

cnf(c_6749,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_2835])).

cnf(c_10991,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6749,c_2680,c_2964])).

cnf(c_10992,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10991])).

cnf(c_11001,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_10992])).

cnf(c_11074,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11001,c_2680,c_2964])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_173,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_33])).

cnf(c_174,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_174])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1353,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_11077,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11074,c_1353])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_547,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_174,c_32])).

cnf(c_548,plain,
    ( sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_804,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1595,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1596,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_803,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1648,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1651,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1779,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1652,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1807,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1808,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_1878,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1879,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1878])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2227,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4943,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_4944,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4943])).

cnf(c_806,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2545,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_3327,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_10774,plain,
    ( ~ r1_tarski(sK1,sK2)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3327])).

cnf(c_11130,plain,
    ( k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11077,c_30,c_95,c_96,c_548,c_1596,c_1648,c_1651,c_1779,c_1808,c_1879,c_2162,c_2227,c_2680,c_2964,c_3208,c_4944,c_10774])).

cnf(c_11133,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3141,c_11130])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11185,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11133,c_29])).

cnf(c_11186,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11185])).

cnf(c_11456,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11186,c_11130])).

cnf(c_3100,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_1372])).

cnf(c_3383,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_1372])).

cnf(c_6322,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_3383])).

cnf(c_7585,plain,
    ( r1_tarski(sK0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6322,c_2680,c_2964])).

cnf(c_7586,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7585])).

cnf(c_1368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3486,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1365])).

cnf(c_7597,plain,
    ( r1_tarski(sK0,sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7586,c_3486])).

cnf(c_86,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1594,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1647,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2228,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2229,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2228])).

cnf(c_2799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1363])).

cnf(c_4451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_2799])).

cnf(c_4521,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4451,c_2680,c_2964])).

cnf(c_4522,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4521])).

cnf(c_4528,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_4522])).

cnf(c_808,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_815,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1616,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_2038,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_2044,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_2046,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_1784,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_2088,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_2089,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_2348,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_805,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2555,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_2557,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_3488,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1365])).

cnf(c_3519,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3488])).

cnf(c_4633,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4528,c_94,c_95,c_96,c_0,c_815,c_1779,c_2046,c_2089,c_2348,c_2557,c_3519])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1359])).

cnf(c_4640,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4633,c_2163])).

cnf(c_5261,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4640,c_2680,c_2964])).

cnf(c_5262,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5261])).

cnf(c_3490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1365])).

cnf(c_3587,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_3490])).

cnf(c_5272,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5262,c_3587])).

cnf(c_5341,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5272])).

cnf(c_7402,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_7403,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7402])).

cnf(c_7405,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7403])).

cnf(c_10182,plain,
    ( v1_xboole_0(k1_relat_1(sK3)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7597,c_29,c_88,c_94,c_95,c_96,c_107,c_1647,c_1648,c_2229,c_5341,c_7405])).

cnf(c_1373,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10189,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10182,c_1373])).

cnf(c_10201,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10189])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11456,c_11130,c_10201,c_3141,c_2557,c_0])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.13/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.00  
% 3.13/1.00  ------  iProver source info
% 3.13/1.00  
% 3.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.00  git: non_committed_changes: false
% 3.13/1.00  git: last_make_outside_of_git: false
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     num_symb
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       true
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  ------ Parsing...
% 3.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.00  ------ Proving...
% 3.13/1.00  ------ Problem Properties 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  clauses                                 28
% 3.13/1.00  conjectures                             3
% 3.13/1.00  EPR                                     8
% 3.13/1.00  Horn                                    25
% 3.13/1.00  unary                                   8
% 3.13/1.00  binary                                  8
% 3.13/1.00  lits                                    64
% 3.13/1.00  lits eq                                 25
% 3.13/1.00  fd_pure                                 0
% 3.13/1.00  fd_pseudo                               0
% 3.13/1.00  fd_cond                                 3
% 3.13/1.00  fd_pseudo_cond                          0
% 3.13/1.00  AC symbols                              0
% 3.13/1.00  
% 3.13/1.00  ------ Schedule dynamic 5 is on 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  Current options:
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     none
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       false
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ Proving...
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS status Theorem for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  fof(f18,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f34,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f35,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(flattening,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f43,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(nnf_transformation,[],[f35])).
% 3.13/1.00  
% 3.13/1.00  fof(f68,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f43])).
% 3.13/1.00  
% 3.13/1.00  fof(f19,conjecture,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f20,negated_conjecture,(
% 3.13/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/1.00    inference(negated_conjecture,[],[f19])).
% 3.13/1.00  
% 3.13/1.00  fof(f36,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f20])).
% 3.13/1.00  
% 3.13/1.00  fof(f37,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.13/1.00    inference(flattening,[],[f36])).
% 3.13/1.00  
% 3.13/1.00  fof(f44,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f45,plain,(
% 3.13/1.00    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f44])).
% 3.13/1.00  
% 3.13/1.00  fof(f75,plain,(
% 3.13/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f76,plain,(
% 3.13/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f16,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f31,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f66,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f31])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f14])).
% 3.13/1.00  
% 3.13/1.00  fof(f63,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f11,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f41,plain,(
% 3.13/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f27])).
% 3.13/1.00  
% 3.13/1.00  fof(f58,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f41])).
% 3.13/1.00  
% 3.13/1.00  fof(f64,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f42,plain,(
% 3.13/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f60,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f42])).
% 3.13/1.00  
% 3.13/1.00  fof(f77,plain,(
% 3.13/1.00    r1_tarski(sK1,sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(ennf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f24,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.13/1.00    inference(flattening,[],[f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f48,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f24])).
% 3.13/1.00  
% 3.13/1.00  fof(f8,axiom,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f40,plain,(
% 3.13/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.13/1.00    inference(nnf_transformation,[],[f8])).
% 3.13/1.00  
% 3.13/1.00  fof(f55,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f10,axiom,(
% 3.13/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f57,plain,(
% 3.13/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f26])).
% 3.13/1.00  
% 3.13/1.00  fof(f56,plain,(
% 3.13/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f13,axiom,(
% 3.13/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f62,plain,(
% 3.13/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f17,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f32,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.13/1.00    inference(ennf_transformation,[],[f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f33,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.13/1.00    inference(flattening,[],[f32])).
% 3.13/1.00  
% 3.13/1.00  fof(f67,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f33])).
% 3.13/1.00  
% 3.13/1.00  fof(f70,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f43])).
% 3.13/1.00  
% 3.13/1.00  fof(f79,plain,(
% 3.13/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f74,plain,(
% 3.13/1.00    v1_funct_1(sK3)),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f6,axiom,(
% 3.13/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f38,plain,(
% 3.13/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/1.00    inference(nnf_transformation,[],[f6])).
% 3.13/1.00  
% 3.13/1.00  fof(f39,plain,(
% 3.13/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/1.00    inference(flattening,[],[f38])).
% 3.13/1.00  
% 3.13/1.00  fof(f51,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f52,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f81,plain,(
% 3.13/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.13/1.00    inference(equality_resolution,[],[f52])).
% 3.13/1.00  
% 3.13/1.00  fof(f5,axiom,(
% 3.13/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f25,plain,(
% 3.13/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.13/1.00    inference(ennf_transformation,[],[f5])).
% 3.13/1.00  
% 3.13/1.00  fof(f50,plain,(
% 3.13/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f25])).
% 3.13/1.00  
% 3.13/1.00  fof(f78,plain,(
% 3.13/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f15,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f65,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f30])).
% 3.13/1.00  
% 3.13/1.00  fof(f7,axiom,(
% 3.13/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f54,plain,(
% 3.13/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    v1_xboole_0(k1_xboole_0)),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f46,plain,(
% 3.13/1.00    v1_xboole_0(k1_xboole_0)),
% 3.13/1.00    inference(cnf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f47,plain,(
% 3.13/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f22])).
% 3.13/1.00  
% 3.13/1.00  fof(f53,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.13/1.00    inference(cnf_transformation,[],[f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f80,plain,(
% 3.13/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.13/1.00    inference(equality_resolution,[],[f53])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_27,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_32,negated_conjecture,
% 3.13/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_536,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.00      | sK1 != X2
% 3.13/1.00      | sK0 != X1
% 3.13/1.00      | sK3 != X0
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_537,plain,
% 3.13/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.13/1.00      | k1_xboole_0 = sK1 ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_31,negated_conjecture,
% 3.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_539,plain,
% 3.13/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_537,c_31]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1361,plain,
% 3.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_20,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1364,plain,
% 3.13/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.13/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2836,plain,
% 3.13/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1361,c_1364]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3141,plain,
% 3.13/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_539,c_2836]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_18,plain,
% 3.13/1.00      ( v4_relat_1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_13,plain,
% 3.13/1.00      ( ~ v4_relat_1(X0,X1)
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_405,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(resolution,[status(thm)],[c_18,c_13]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1359,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2162,plain,
% 3.13/1.00      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 3.13/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1361,c_1359]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_17,plain,
% 3.13/1.00      ( v5_relat_1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_15,plain,
% 3.13/1.00      ( ~ v5_relat_1(X0,X1)
% 3.13/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_424,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(resolution,[status(thm)],[c_17,c_15]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1358,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1742,plain,
% 3.13/1.00      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 3.13/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1361,c_1358]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_30,negated_conjecture,
% 3.13/1.00      ( r1_tarski(sK1,sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1362,plain,
% 3.13/1.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1372,plain,
% 3.13/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.13/1.00      | r1_tarski(X2,X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3099,plain,
% 3.13/1.00      ( r1_tarski(X0,sK1) != iProver_top
% 3.13/1.00      | r1_tarski(X0,sK2) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1362,c_1372]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3208,plain,
% 3.13/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 3.13/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1742,c_3099]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_10,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1367,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.13/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2305,plain,
% 3.13/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1361,c_1367]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_11,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ v1_relat_1(X1)
% 3.13/1.00      | v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_9,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_242,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.13/1.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_243,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_242]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_303,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.13/1.00      inference(bin_hyper_res,[status(thm)],[c_11,c_243]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1360,plain,
% 3.13/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.13/1.00      | v1_relat_1(X1) != iProver_top
% 3.13/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2680,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.13/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2305,c_1360]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_16,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2963,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2964,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3361,plain,
% 3.13/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3208,c_2680,c_2964]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_21,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.13/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1363,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.13/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2835,plain,
% 3.13/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.13/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.13/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.13/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1363,c_1364]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6749,plain,
% 3.13/1.00      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.13/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.13/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_3361,c_2835]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_10991,plain,
% 3.13/1.00      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.13/1.00      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_6749,c_2680,c_2964]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_10992,plain,
% 3.13/1.00      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.13/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_10991]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_11001,plain,
% 3.13/1.00      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
% 3.13/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2162,c_10992]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_11074,plain,
% 3.13/1.00      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_11001,c_2680,c_2964]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_25,plain,
% 3.13/1.01      ( v1_funct_2(X0,X1,X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_28,negated_conjecture,
% 3.13/1.01      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.13/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | ~ v1_funct_1(sK3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_33,negated_conjecture,
% 3.13/1.01      ( v1_funct_1(sK3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_173,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_28,c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_174,negated_conjecture,
% 3.13/1.01      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.13/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_173]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_523,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.13/1.01      | sK2 != X2
% 3.13/1.01      | sK0 != X1
% 3.13/1.01      | sK3 != X0
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_174]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_524,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | k1_relset_1(sK0,sK2,sK3) != sK0
% 3.13/1.01      | k1_xboole_0 = sK2 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_523]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1353,plain,
% 3.13/1.01      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 3.13/1.01      | k1_xboole_0 = sK2
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11077,plain,
% 3.13/1.01      ( k1_relat_1(sK3) != sK0
% 3.13/1.01      | sK2 = k1_xboole_0
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_11074,c_1353]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7,plain,
% 3.13/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.13/1.01      | k1_xboole_0 = X0
% 3.13/1.01      | k1_xboole_0 = X1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_95,plain,
% 3.13/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.13/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6,plain,
% 3.13/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_96,plain,
% 3.13/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_547,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | sK1 != sK2
% 3.13/1.01      | sK0 != sK0
% 3.13/1.01      | sK3 != sK3 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_174,c_32]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_548,plain,
% 3.13/1.01      ( sK1 != sK2
% 3.13/1.01      | sK0 != sK0
% 3.13/1.01      | sK3 != sK3
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_804,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1595,plain,
% 3.13/1.01      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1596,plain,
% 3.13/1.01      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_803,plain,( X0 = X0 ),theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1648,plain,
% 3.13/1.01      ( sK0 = sK0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_803]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1651,plain,
% 3.13/1.01      ( sK1 = sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_803]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1779,plain,
% 3.13/1.01      ( sK3 = sK3 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_803]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1652,plain,
% 3.13/1.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1807,plain,
% 3.13/1.01      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1652]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1808,plain,
% 3.13/1.01      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1807]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1878,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.13/1.01      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.13/1.01      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.13/1.01      | ~ v1_relat_1(sK3) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1879,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1878]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2227,plain,
% 3.13/1.01      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4943,plain,
% 3.13/1.01      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4944,plain,
% 3.13/1.01      ( sK2 != k1_xboole_0
% 3.13/1.01      | k1_xboole_0 = sK2
% 3.13/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_4943]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_806,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2545,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1)
% 3.13/1.01      | r1_tarski(sK1,k1_xboole_0)
% 3.13/1.01      | sK1 != X0
% 3.13/1.01      | k1_xboole_0 != X1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3327,plain,
% 3.13/1.01      ( ~ r1_tarski(sK1,X0)
% 3.13/1.01      | r1_tarski(sK1,k1_xboole_0)
% 3.13/1.01      | sK1 != sK1
% 3.13/1.01      | k1_xboole_0 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2545]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10774,plain,
% 3.13/1.01      ( ~ r1_tarski(sK1,sK2)
% 3.13/1.01      | r1_tarski(sK1,k1_xboole_0)
% 3.13/1.01      | sK1 != sK1
% 3.13/1.01      | k1_xboole_0 != sK2 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_3327]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11130,plain,
% 3.13/1.01      ( k1_relat_1(sK3) != sK0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_11077,c_30,c_95,c_96,c_548,c_1596,c_1648,c_1651,
% 3.13/1.01                 c_1779,c_1808,c_1879,c_2162,c_2227,c_2680,c_2964,c_3208,
% 3.13/1.01                 c_4944,c_10774]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11133,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3141,c_11130]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_29,negated_conjecture,
% 3.13/1.01      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11185,plain,
% 3.13/1.01      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_11133,c_29]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11186,plain,
% 3.13/1.01      ( sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_11185]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11456,plain,
% 3.13/1.01      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_11186,c_11130]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3100,plain,
% 3.13/1.01      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.13/1.01      | r1_tarski(X0,sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2305,c_1372]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3383,plain,
% 3.13/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.13/1.01      | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.13/1.01      | r1_tarski(X1,sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3100,c_1372]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6322,plain,
% 3.13/1.01      ( r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,sK3) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2162,c_3383]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7585,plain,
% 3.13/1.01      ( r1_tarski(sK0,sK3) != iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_6322,c_2680,c_2964]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7586,plain,
% 3.13/1.01      ( r1_tarski(k1_relat_1(sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,sK3) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_7585]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1368,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.13/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_19,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_xboole_0(X2)
% 3.13/1.01      | v1_xboole_0(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1365,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | v1_xboole_0(X2) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3486,plain,
% 3.13/1.01      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.13/1.01      | v1_xboole_0(X2) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1368,c_1365]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7597,plain,
% 3.13/1.01      ( r1_tarski(sK0,sK3) != iProver_top
% 3.13/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top
% 3.13/1.01      | v1_xboole_0(sK1) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_7586,c_3486]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_86,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.13/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_88,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.13/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_86]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_92,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_94,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_92]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_0,plain,
% 3.13/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_107,plain,
% 3.13/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1594,plain,
% 3.13/1.01      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1647,plain,
% 3.13/1.01      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2228,plain,
% 3.13/1.01      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2229,plain,
% 3.13/1.01      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2228]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2799,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_6,c_1363]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4451,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1742,c_2799]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4521,plain,
% 3.13/1.01      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_4451,c_2680,c_2964]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4522,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_4521]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4528,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3141,c_4522]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_808,plain,
% 3.13/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_815,plain,
% 3.13/1.01      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 3.13/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_808]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_809,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1616,plain,
% 3.13/1.01      ( m1_subset_1(X0,X1)
% 3.13/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.13/1.01      | X1 != k1_zfmisc_1(X2)
% 3.13/1.01      | X0 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_809]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1709,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.13/1.01      | X0 != k1_xboole_0
% 3.13/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1616]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2038,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.13/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.13/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 3.13/1.01      | sK3 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1709]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2044,plain,
% 3.13/1.01      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 3.13/1.01      | sK3 != k1_xboole_0
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 3.13/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2038]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2046,plain,
% 3.13/1.01      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.13/1.01      | sK3 != k1_xboole_0
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2044]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1784,plain,
% 3.13/1.01      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2088,plain,
% 3.13/1.01      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1784]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2089,plain,
% 3.13/1.01      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2348,plain,
% 3.13/1.01      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_805,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2555,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_805]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2557,plain,
% 3.13/1.01      ( v1_xboole_0(sK1)
% 3.13/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.13/1.01      | sK1 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2555]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3488,plain,
% 3.13/1.01      ( v1_xboole_0(sK1) != iProver_top
% 3.13/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1361,c_1365]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3519,plain,
% 3.13/1.01      ( ~ v1_xboole_0(sK1) | v1_xboole_0(sK3) ),
% 3.13/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3488]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4633,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_4528,c_94,c_95,c_96,c_0,c_815,c_1779,c_2046,c_2089,
% 3.13/1.01                 c_2348,c_2557,c_3519]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5,plain,
% 3.13/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2163,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5,c_1359]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4640,plain,
% 3.13/1.01      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_4633,c_2163]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5261,plain,
% 3.13/1.01      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.13/1.01      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_4640,c_2680,c_2964]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5262,plain,
% 3.13/1.01      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_5261]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3490,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.13/1.01      | v1_xboole_0(X1) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_6,c_1365]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3587,plain,
% 3.13/1.01      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_xboole_0(X1) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1368,c_3490]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5272,plain,
% 3.13/1.01      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) != iProver_top
% 3.13/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5262,c_3587]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5341,plain,
% 3.13/1.01      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.13/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top
% 3.13/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_5272]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7402,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1)
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0)
% 3.13/1.01      | sK0 != X0
% 3.13/1.01      | k1_xboole_0 != X1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7403,plain,
% 3.13/1.01      ( sK0 != X0
% 3.13/1.01      | k1_xboole_0 != X1
% 3.13/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_7402]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7405,plain,
% 3.13/1.01      ( sK0 != k1_xboole_0
% 3.13/1.01      | k1_xboole_0 != k1_xboole_0
% 3.13/1.01      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 3.13/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_7403]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10182,plain,
% 3.13/1.01      ( v1_xboole_0(k1_relat_1(sK3)) = iProver_top
% 3.13/1.01      | v1_xboole_0(sK1) != iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_7597,c_29,c_88,c_94,c_95,c_96,c_107,c_1647,c_1648,
% 3.13/1.01                 c_2229,c_5341,c_7405]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1373,plain,
% 3.13/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10189,plain,
% 3.13/1.01      ( k1_relat_1(sK3) = k1_xboole_0 | v1_xboole_0(sK1) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_10182,c_1373]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10201,plain,
% 3.13/1.01      ( ~ v1_xboole_0(sK1) | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.13/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_10189]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(contradiction,plain,
% 3.13/1.01      ( $false ),
% 3.13/1.01      inference(minisat,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_11456,c_11130,c_10201,c_3141,c_2557,c_0]) ).
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  ------                               Statistics
% 3.13/1.01  
% 3.13/1.01  ------ General
% 3.13/1.01  
% 3.13/1.01  abstr_ref_over_cycles:                  0
% 3.13/1.01  abstr_ref_under_cycles:                 0
% 3.13/1.01  gc_basic_clause_elim:                   0
% 3.13/1.01  forced_gc_time:                         0
% 3.13/1.01  parsing_time:                           0.012
% 3.13/1.01  unif_index_cands_time:                  0.
% 3.13/1.01  unif_index_add_time:                    0.
% 3.13/1.01  orderings_time:                         0.
% 3.13/1.01  out_proof_time:                         0.012
% 3.13/1.01  total_time:                             0.289
% 3.13/1.01  num_of_symbols:                         49
% 3.13/1.01  num_of_terms:                           6059
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing
% 3.13/1.01  
% 3.13/1.01  num_of_splits:                          0
% 3.13/1.01  num_of_split_atoms:                     0
% 3.13/1.01  num_of_reused_defs:                     0
% 3.13/1.01  num_eq_ax_congr_red:                    12
% 3.13/1.01  num_of_sem_filtered_clauses:            2
% 3.13/1.01  num_of_subtypes:                        0
% 3.13/1.01  monotx_restored_types:                  0
% 3.13/1.01  sat_num_of_epr_types:                   0
% 3.13/1.01  sat_num_of_non_cyclic_types:            0
% 3.13/1.01  sat_guarded_non_collapsed_types:        0
% 3.13/1.01  num_pure_diseq_elim:                    0
% 3.13/1.01  simp_replaced_by:                       0
% 3.13/1.01  res_preprocessed:                       137
% 3.13/1.01  prep_upred:                             0
% 3.13/1.01  prep_unflattend:                        33
% 3.13/1.01  smt_new_axioms:                         0
% 3.13/1.01  pred_elim_cands:                        4
% 3.13/1.01  pred_elim:                              3
% 3.13/1.01  pred_elim_cl:                           5
% 3.13/1.01  pred_elim_cycles:                       5
% 3.13/1.01  merged_defs:                            8
% 3.13/1.01  merged_defs_ncl:                        0
% 3.13/1.01  bin_hyper_res:                          9
% 3.13/1.01  prep_cycles:                            4
% 3.13/1.01  pred_elim_time:                         0.005
% 3.13/1.01  splitting_time:                         0.
% 3.13/1.01  sem_filter_time:                        0.
% 3.13/1.01  monotx_time:                            0.
% 3.13/1.01  subtype_inf_time:                       0.
% 3.13/1.01  
% 3.13/1.01  ------ Problem properties
% 3.13/1.01  
% 3.13/1.01  clauses:                                28
% 3.13/1.01  conjectures:                            3
% 3.13/1.01  epr:                                    8
% 3.13/1.01  horn:                                   25
% 3.13/1.01  ground:                                 11
% 3.13/1.01  unary:                                  8
% 3.13/1.01  binary:                                 8
% 3.13/1.01  lits:                                   64
% 3.13/1.01  lits_eq:                                25
% 3.13/1.01  fd_pure:                                0
% 3.13/1.01  fd_pseudo:                              0
% 3.13/1.01  fd_cond:                                3
% 3.13/1.01  fd_pseudo_cond:                         0
% 3.13/1.01  ac_symbols:                             0
% 3.13/1.01  
% 3.13/1.01  ------ Propositional Solver
% 3.13/1.01  
% 3.13/1.01  prop_solver_calls:                      30
% 3.13/1.01  prop_fast_solver_calls:                 1130
% 3.13/1.01  smt_solver_calls:                       0
% 3.13/1.01  smt_fast_solver_calls:                  0
% 3.13/1.01  prop_num_of_clauses:                    3554
% 3.13/1.01  prop_preprocess_simplified:             7720
% 3.13/1.01  prop_fo_subsumed:                       42
% 3.13/1.01  prop_solver_time:                       0.
% 3.13/1.01  smt_solver_time:                        0.
% 3.13/1.01  smt_fast_solver_time:                   0.
% 3.13/1.01  prop_fast_solver_time:                  0.
% 3.13/1.01  prop_unsat_core_time:                   0.
% 3.13/1.01  
% 3.13/1.01  ------ QBF
% 3.13/1.01  
% 3.13/1.01  qbf_q_res:                              0
% 3.13/1.01  qbf_num_tautologies:                    0
% 3.13/1.01  qbf_prep_cycles:                        0
% 3.13/1.01  
% 3.13/1.01  ------ BMC1
% 3.13/1.01  
% 3.13/1.01  bmc1_current_bound:                     -1
% 3.13/1.01  bmc1_last_solved_bound:                 -1
% 3.13/1.01  bmc1_unsat_core_size:                   -1
% 3.13/1.01  bmc1_unsat_core_parents_size:           -1
% 3.13/1.01  bmc1_merge_next_fun:                    0
% 3.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation
% 3.13/1.01  
% 3.13/1.01  inst_num_of_clauses:                    1041
% 3.13/1.01  inst_num_in_passive:                    97
% 3.13/1.01  inst_num_in_active:                     547
% 3.13/1.01  inst_num_in_unprocessed:                397
% 3.13/1.01  inst_num_of_loops:                      730
% 3.13/1.01  inst_num_of_learning_restarts:          0
% 3.13/1.01  inst_num_moves_active_passive:          179
% 3.13/1.01  inst_lit_activity:                      0
% 3.13/1.01  inst_lit_activity_moves:                0
% 3.13/1.01  inst_num_tautologies:                   0
% 3.13/1.01  inst_num_prop_implied:                  0
% 3.13/1.01  inst_num_existing_simplified:           0
% 3.13/1.01  inst_num_eq_res_simplified:             0
% 3.13/1.01  inst_num_child_elim:                    0
% 3.13/1.01  inst_num_of_dismatching_blockings:      735
% 3.13/1.01  inst_num_of_non_proper_insts:           1593
% 3.13/1.01  inst_num_of_duplicates:                 0
% 3.13/1.01  inst_inst_num_from_inst_to_res:         0
% 3.13/1.01  inst_dismatching_checking_time:         0.
% 3.13/1.01  
% 3.13/1.01  ------ Resolution
% 3.13/1.01  
% 3.13/1.01  res_num_of_clauses:                     0
% 3.13/1.01  res_num_in_passive:                     0
% 3.13/1.01  res_num_in_active:                      0
% 3.13/1.01  res_num_of_loops:                       141
% 3.13/1.01  res_forward_subset_subsumed:            40
% 3.13/1.01  res_backward_subset_subsumed:           8
% 3.13/1.01  res_forward_subsumed:                   0
% 3.13/1.01  res_backward_subsumed:                  0
% 3.13/1.01  res_forward_subsumption_resolution:     1
% 3.13/1.01  res_backward_subsumption_resolution:    0
% 3.13/1.01  res_clause_to_clause_subsumption:       1365
% 3.13/1.01  res_orphan_elimination:                 0
% 3.13/1.01  res_tautology_del:                      151
% 3.13/1.01  res_num_eq_res_simplified:              1
% 3.13/1.01  res_num_sel_changes:                    0
% 3.13/1.01  res_moves_from_active_to_pass:          0
% 3.13/1.01  
% 3.13/1.01  ------ Superposition
% 3.13/1.01  
% 3.13/1.01  sup_time_total:                         0.
% 3.13/1.01  sup_time_generating:                    0.
% 3.13/1.01  sup_time_sim_full:                      0.
% 3.13/1.01  sup_time_sim_immed:                     0.
% 3.13/1.01  
% 3.13/1.01  sup_num_of_clauses:                     210
% 3.13/1.01  sup_num_in_active:                      62
% 3.13/1.01  sup_num_in_passive:                     148
% 3.13/1.01  sup_num_of_loops:                       144
% 3.13/1.01  sup_fw_superposition:                   271
% 3.13/1.01  sup_bw_superposition:                   226
% 3.13/1.01  sup_immediate_simplified:               208
% 3.13/1.01  sup_given_eliminated:                   0
% 3.13/1.01  comparisons_done:                       0
% 3.13/1.01  comparisons_avoided:                    3
% 3.13/1.01  
% 3.13/1.01  ------ Simplifications
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  sim_fw_subset_subsumed:                 42
% 3.13/1.01  sim_bw_subset_subsumed:                 19
% 3.13/1.01  sim_fw_subsumed:                        99
% 3.13/1.01  sim_bw_subsumed:                        13
% 3.13/1.01  sim_fw_subsumption_res:                 10
% 3.13/1.01  sim_bw_subsumption_res:                 0
% 3.13/1.01  sim_tautology_del:                      29
% 3.13/1.01  sim_eq_tautology_del:                   7
% 3.13/1.01  sim_eq_res_simp:                        4
% 3.13/1.01  sim_fw_demodulated:                     19
% 3.13/1.01  sim_bw_demodulated:                     75
% 3.13/1.01  sim_light_normalised:                   50
% 3.13/1.01  sim_joinable_taut:                      0
% 3.13/1.01  sim_joinable_simp:                      0
% 3.13/1.01  sim_ac_normalised:                      0
% 3.13/1.01  sim_smt_subsumption:                    0
% 3.13/1.01  
%------------------------------------------------------------------------------
