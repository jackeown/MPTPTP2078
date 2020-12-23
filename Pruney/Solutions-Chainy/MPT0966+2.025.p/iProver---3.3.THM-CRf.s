%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:35 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  208 (6842 expanded)
%              Number of clauses        :  140 (2662 expanded)
%              Number of leaves         :   17 (1229 expanded)
%              Depth                    :   30
%              Number of atoms          :  623 (32540 expanded)
%              Number of equality atoms :  353 (10278 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f39])).

fof(f67,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_473,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_475,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_28])).

cnf(c_1234,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1238,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3104,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1234,c_1238])).

cnf(c_3190,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_3104])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_13])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1605,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_1232])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1237,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2301,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1234,c_1237])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1235,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2410,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2301,c_1235])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3103,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1238])).

cnf(c_11852,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_3103])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2141,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_1240])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_217])).

cnf(c_1233,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2326,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_1233])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1239,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2503,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2326,c_1239])).

cnf(c_12274,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11852,c_2503])).

cnf(c_12275,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12274])).

cnf(c_12285,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_12275])).

cnf(c_12456,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12285,c_2503])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_155,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_30])).

cnf(c_156,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_156])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1227,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_12459,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12456,c_1227])).

cnf(c_1769,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1770,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_12462,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12459,c_1605,c_1770,c_2410,c_2503])).

cnf(c_12463,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12462])).

cnf(c_12466,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3190,c_12463])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12601,plain,
    ( sK2 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12466,c_26])).

cnf(c_19,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK0 != X0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_156])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_400,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_388,c_8])).

cnf(c_1231,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_12643,plain,
    ( sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12601,c_1231])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1427,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | r1_tarski(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1630,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1999,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2117,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1236])).

cnf(c_3419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_2654])).

cnf(c_3629,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_2503])).

cnf(c_3630,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3629])).

cnf(c_3631,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3630])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2149,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1232])).

cnf(c_3714,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2149])).

cnf(c_3734,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_3714])).

cnf(c_76,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_82,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_84,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_726,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1498,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1499,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_1501,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1230,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1326,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_5])).

cnf(c_725,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1443,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1515,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_724,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1516,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1619,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1620,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_1779,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1326,c_26,c_85,c_86,c_1515,c_1516,c_1620])).

cnf(c_4072,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3734,c_78,c_84,c_85,c_86,c_1501,c_1779,c_2503])).

cnf(c_4073,plain,
    ( r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4072])).

cnf(c_4074,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4073])).

cnf(c_12641,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12601,c_2410])).

cnf(c_12680,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12641])).

cnf(c_12855,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12643,c_1427,c_1630,c_1999,c_2117,c_3631,c_4074,c_12680])).

cnf(c_12859,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_12855,c_12456])).

cnf(c_12913,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_12855,c_3104])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_447,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_1228,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_1319,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1228,c_6])).

cnf(c_12921,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12855,c_1319])).

cnf(c_12938,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12921])).

cnf(c_12924,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12855,c_1234])).

cnf(c_12927,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12924,c_6])).

cnf(c_12941,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12938,c_12927])).

cnf(c_12964,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12913,c_12941])).

cnf(c_13140,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12859,c_12964])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_156])).

cnf(c_431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1229,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_1357,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1229,c_6])).

cnf(c_12918,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12855,c_1357])).

cnf(c_12947,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12918])).

cnf(c_12951,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12947,c_12927])).

cnf(c_12952,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12951,c_6])).

cnf(c_13142,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13140,c_12952])).

cnf(c_13144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13142])).

cnf(c_13146,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13144,c_12927])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:23:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.63/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.99  
% 3.63/0.99  ------  iProver source info
% 3.63/0.99  
% 3.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.99  git: non_committed_changes: false
% 3.63/0.99  git: last_make_outside_of_git: false
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options
% 3.63/0.99  
% 3.63/0.99  --out_options                           all
% 3.63/0.99  --tptp_safe_out                         true
% 3.63/0.99  --problem_path                          ""
% 3.63/0.99  --include_path                          ""
% 3.63/0.99  --clausifier                            res/vclausify_rel
% 3.63/0.99  --clausifier_options                    --mode clausify
% 3.63/0.99  --stdin                                 false
% 3.63/0.99  --stats_out                             all
% 3.63/0.99  
% 3.63/0.99  ------ General Options
% 3.63/0.99  
% 3.63/0.99  --fof                                   false
% 3.63/0.99  --time_out_real                         305.
% 3.63/0.99  --time_out_virtual                      -1.
% 3.63/0.99  --symbol_type_check                     false
% 3.63/0.99  --clausify_out                          false
% 3.63/0.99  --sig_cnt_out                           false
% 3.63/0.99  --trig_cnt_out                          false
% 3.63/0.99  --trig_cnt_out_tolerance                1.
% 3.63/0.99  --trig_cnt_out_sk_spl                   false
% 3.63/0.99  --abstr_cl_out                          false
% 3.63/0.99  
% 3.63/0.99  ------ Global Options
% 3.63/0.99  
% 3.63/0.99  --schedule                              default
% 3.63/0.99  --add_important_lit                     false
% 3.63/0.99  --prop_solver_per_cl                    1000
% 3.63/0.99  --min_unsat_core                        false
% 3.63/0.99  --soft_assumptions                      false
% 3.63/0.99  --soft_lemma_size                       3
% 3.63/0.99  --prop_impl_unit_size                   0
% 3.63/0.99  --prop_impl_unit                        []
% 3.63/0.99  --share_sel_clauses                     true
% 3.63/0.99  --reset_solvers                         false
% 3.63/0.99  --bc_imp_inh                            [conj_cone]
% 3.63/0.99  --conj_cone_tolerance                   3.
% 3.63/0.99  --extra_neg_conj                        none
% 3.63/0.99  --large_theory_mode                     true
% 3.63/0.99  --prolific_symb_bound                   200
% 3.63/0.99  --lt_threshold                          2000
% 3.63/0.99  --clause_weak_htbl                      true
% 3.63/0.99  --gc_record_bc_elim                     false
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing Options
% 3.63/0.99  
% 3.63/0.99  --preprocessing_flag                    true
% 3.63/0.99  --time_out_prep_mult                    0.1
% 3.63/0.99  --splitting_mode                        input
% 3.63/0.99  --splitting_grd                         true
% 3.63/0.99  --splitting_cvd                         false
% 3.63/0.99  --splitting_cvd_svl                     false
% 3.63/0.99  --splitting_nvd                         32
% 3.63/0.99  --sub_typing                            true
% 3.63/0.99  --prep_gs_sim                           true
% 3.63/0.99  --prep_unflatten                        true
% 3.63/0.99  --prep_res_sim                          true
% 3.63/0.99  --prep_upred                            true
% 3.63/0.99  --prep_sem_filter                       exhaustive
% 3.63/0.99  --prep_sem_filter_out                   false
% 3.63/0.99  --pred_elim                             true
% 3.63/0.99  --res_sim_input                         true
% 3.63/0.99  --eq_ax_congr_red                       true
% 3.63/0.99  --pure_diseq_elim                       true
% 3.63/0.99  --brand_transform                       false
% 3.63/0.99  --non_eq_to_eq                          false
% 3.63/0.99  --prep_def_merge                        true
% 3.63/0.99  --prep_def_merge_prop_impl              false
% 3.63/0.99  --prep_def_merge_mbd                    true
% 3.63/0.99  --prep_def_merge_tr_red                 false
% 3.63/0.99  --prep_def_merge_tr_cl                  false
% 3.63/0.99  --smt_preprocessing                     true
% 3.63/0.99  --smt_ac_axioms                         fast
% 3.63/0.99  --preprocessed_out                      false
% 3.63/0.99  --preprocessed_stats                    false
% 3.63/0.99  
% 3.63/0.99  ------ Abstraction refinement Options
% 3.63/0.99  
% 3.63/0.99  --abstr_ref                             []
% 3.63/0.99  --abstr_ref_prep                        false
% 3.63/0.99  --abstr_ref_until_sat                   false
% 3.63/0.99  --abstr_ref_sig_restrict                funpre
% 3.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.99  --abstr_ref_under                       []
% 3.63/0.99  
% 3.63/0.99  ------ SAT Options
% 3.63/0.99  
% 3.63/0.99  --sat_mode                              false
% 3.63/0.99  --sat_fm_restart_options                ""
% 3.63/0.99  --sat_gr_def                            false
% 3.63/0.99  --sat_epr_types                         true
% 3.63/0.99  --sat_non_cyclic_types                  false
% 3.63/0.99  --sat_finite_models                     false
% 3.63/0.99  --sat_fm_lemmas                         false
% 3.63/0.99  --sat_fm_prep                           false
% 3.63/0.99  --sat_fm_uc_incr                        true
% 3.63/0.99  --sat_out_model                         small
% 3.63/0.99  --sat_out_clauses                       false
% 3.63/0.99  
% 3.63/0.99  ------ QBF Options
% 3.63/0.99  
% 3.63/0.99  --qbf_mode                              false
% 3.63/0.99  --qbf_elim_univ                         false
% 3.63/0.99  --qbf_dom_inst                          none
% 3.63/0.99  --qbf_dom_pre_inst                      false
% 3.63/0.99  --qbf_sk_in                             false
% 3.63/0.99  --qbf_pred_elim                         true
% 3.63/0.99  --qbf_split                             512
% 3.63/0.99  
% 3.63/0.99  ------ BMC1 Options
% 3.63/0.99  
% 3.63/0.99  --bmc1_incremental                      false
% 3.63/0.99  --bmc1_axioms                           reachable_all
% 3.63/0.99  --bmc1_min_bound                        0
% 3.63/0.99  --bmc1_max_bound                        -1
% 3.63/0.99  --bmc1_max_bound_default                -1
% 3.63/0.99  --bmc1_symbol_reachability              true
% 3.63/0.99  --bmc1_property_lemmas                  false
% 3.63/0.99  --bmc1_k_induction                      false
% 3.63/0.99  --bmc1_non_equiv_states                 false
% 3.63/0.99  --bmc1_deadlock                         false
% 3.63/0.99  --bmc1_ucm                              false
% 3.63/0.99  --bmc1_add_unsat_core                   none
% 3.63/0.99  --bmc1_unsat_core_children              false
% 3.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.99  --bmc1_out_stat                         full
% 3.63/0.99  --bmc1_ground_init                      false
% 3.63/0.99  --bmc1_pre_inst_next_state              false
% 3.63/0.99  --bmc1_pre_inst_state                   false
% 3.63/0.99  --bmc1_pre_inst_reach_state             false
% 3.63/0.99  --bmc1_out_unsat_core                   false
% 3.63/0.99  --bmc1_aig_witness_out                  false
% 3.63/0.99  --bmc1_verbose                          false
% 3.63/0.99  --bmc1_dump_clauses_tptp                false
% 3.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.99  --bmc1_dump_file                        -
% 3.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.99  --bmc1_ucm_extend_mode                  1
% 3.63/0.99  --bmc1_ucm_init_mode                    2
% 3.63/0.99  --bmc1_ucm_cone_mode                    none
% 3.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.99  --bmc1_ucm_relax_model                  4
% 3.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.99  --bmc1_ucm_layered_model                none
% 3.63/0.99  --bmc1_ucm_max_lemma_size               10
% 3.63/0.99  
% 3.63/0.99  ------ AIG Options
% 3.63/0.99  
% 3.63/0.99  --aig_mode                              false
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation Options
% 3.63/0.99  
% 3.63/0.99  --instantiation_flag                    true
% 3.63/0.99  --inst_sos_flag                         false
% 3.63/0.99  --inst_sos_phase                        true
% 3.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel_side                     num_symb
% 3.63/0.99  --inst_solver_per_active                1400
% 3.63/0.99  --inst_solver_calls_frac                1.
% 3.63/0.99  --inst_passive_queue_type               priority_queues
% 3.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.99  --inst_passive_queues_freq              [25;2]
% 3.63/0.99  --inst_dismatching                      true
% 3.63/0.99  --inst_eager_unprocessed_to_passive     true
% 3.63/0.99  --inst_prop_sim_given                   true
% 3.63/0.99  --inst_prop_sim_new                     false
% 3.63/0.99  --inst_subs_new                         false
% 3.63/0.99  --inst_eq_res_simp                      false
% 3.63/0.99  --inst_subs_given                       false
% 3.63/0.99  --inst_orphan_elimination               true
% 3.63/0.99  --inst_learning_loop_flag               true
% 3.63/0.99  --inst_learning_start                   3000
% 3.63/0.99  --inst_learning_factor                  2
% 3.63/0.99  --inst_start_prop_sim_after_learn       3
% 3.63/0.99  --inst_sel_renew                        solver
% 3.63/0.99  --inst_lit_activity_flag                true
% 3.63/0.99  --inst_restr_to_given                   false
% 3.63/0.99  --inst_activity_threshold               500
% 3.63/0.99  --inst_out_proof                        true
% 3.63/0.99  
% 3.63/0.99  ------ Resolution Options
% 3.63/0.99  
% 3.63/0.99  --resolution_flag                       true
% 3.63/0.99  --res_lit_sel                           adaptive
% 3.63/0.99  --res_lit_sel_side                      none
% 3.63/0.99  --res_ordering                          kbo
% 3.63/0.99  --res_to_prop_solver                    active
% 3.63/0.99  --res_prop_simpl_new                    false
% 3.63/0.99  --res_prop_simpl_given                  true
% 3.63/0.99  --res_passive_queue_type                priority_queues
% 3.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.99  --res_passive_queues_freq               [15;5]
% 3.63/0.99  --res_forward_subs                      full
% 3.63/0.99  --res_backward_subs                     full
% 3.63/0.99  --res_forward_subs_resolution           true
% 3.63/0.99  --res_backward_subs_resolution          true
% 3.63/0.99  --res_orphan_elimination                true
% 3.63/0.99  --res_time_limit                        2.
% 3.63/0.99  --res_out_proof                         true
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Options
% 3.63/0.99  
% 3.63/0.99  --superposition_flag                    true
% 3.63/0.99  --sup_passive_queue_type                priority_queues
% 3.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.99  --demod_completeness_check              fast
% 3.63/0.99  --demod_use_ground                      true
% 3.63/0.99  --sup_to_prop_solver                    passive
% 3.63/0.99  --sup_prop_simpl_new                    true
% 3.63/0.99  --sup_prop_simpl_given                  true
% 3.63/0.99  --sup_fun_splitting                     false
% 3.63/0.99  --sup_smt_interval                      50000
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Simplification Setup
% 3.63/0.99  
% 3.63/0.99  --sup_indices_passive                   []
% 3.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_full_bw                           [BwDemod]
% 3.63/0.99  --sup_immed_triv                        [TrivRules]
% 3.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_immed_bw_main                     []
% 3.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  
% 3.63/0.99  ------ Combination Options
% 3.63/0.99  
% 3.63/0.99  --comb_res_mult                         3
% 3.63/0.99  --comb_sup_mult                         2
% 3.63/0.99  --comb_inst_mult                        10
% 3.63/0.99  
% 3.63/0.99  ------ Debug Options
% 3.63/0.99  
% 3.63/0.99  --dbg_backtrace                         false
% 3.63/0.99  --dbg_dump_prop_clauses                 false
% 3.63/0.99  --dbg_dump_prop_clauses_file            -
% 3.63/0.99  --dbg_out_stat                          false
% 3.63/0.99  ------ Parsing...
% 3.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  ------ Proving...
% 3.63/0.99  ------ Problem Properties 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  clauses                                 26
% 3.63/0.99  conjectures                             3
% 3.63/0.99  EPR                                     6
% 3.63/0.99  Horn                                    23
% 3.63/0.99  unary                                   8
% 3.63/0.99  binary                                  8
% 3.63/0.99  lits                                    58
% 3.63/0.99  lits eq                                 26
% 3.63/0.99  fd_pure                                 0
% 3.63/0.99  fd_pseudo                               0
% 3.63/0.99  fd_cond                                 2
% 3.63/0.99  fd_pseudo_cond                          1
% 3.63/0.99  AC symbols                              0
% 3.63/0.99  
% 3.63/0.99  ------ Schedule dynamic 5 is on 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  Current options:
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options
% 3.63/0.99  
% 3.63/0.99  --out_options                           all
% 3.63/0.99  --tptp_safe_out                         true
% 3.63/0.99  --problem_path                          ""
% 3.63/0.99  --include_path                          ""
% 3.63/0.99  --clausifier                            res/vclausify_rel
% 3.63/0.99  --clausifier_options                    --mode clausify
% 3.63/0.99  --stdin                                 false
% 3.63/0.99  --stats_out                             all
% 3.63/0.99  
% 3.63/0.99  ------ General Options
% 3.63/0.99  
% 3.63/0.99  --fof                                   false
% 3.63/0.99  --time_out_real                         305.
% 3.63/0.99  --time_out_virtual                      -1.
% 3.63/0.99  --symbol_type_check                     false
% 3.63/0.99  --clausify_out                          false
% 3.63/0.99  --sig_cnt_out                           false
% 3.63/0.99  --trig_cnt_out                          false
% 3.63/0.99  --trig_cnt_out_tolerance                1.
% 3.63/0.99  --trig_cnt_out_sk_spl                   false
% 3.63/0.99  --abstr_cl_out                          false
% 3.63/0.99  
% 3.63/0.99  ------ Global Options
% 3.63/0.99  
% 3.63/0.99  --schedule                              default
% 3.63/0.99  --add_important_lit                     false
% 3.63/0.99  --prop_solver_per_cl                    1000
% 3.63/0.99  --min_unsat_core                        false
% 3.63/0.99  --soft_assumptions                      false
% 3.63/0.99  --soft_lemma_size                       3
% 3.63/0.99  --prop_impl_unit_size                   0
% 3.63/0.99  --prop_impl_unit                        []
% 3.63/0.99  --share_sel_clauses                     true
% 3.63/0.99  --reset_solvers                         false
% 3.63/0.99  --bc_imp_inh                            [conj_cone]
% 3.63/0.99  --conj_cone_tolerance                   3.
% 3.63/0.99  --extra_neg_conj                        none
% 3.63/0.99  --large_theory_mode                     true
% 3.63/0.99  --prolific_symb_bound                   200
% 3.63/0.99  --lt_threshold                          2000
% 3.63/0.99  --clause_weak_htbl                      true
% 3.63/0.99  --gc_record_bc_elim                     false
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing Options
% 3.63/0.99  
% 3.63/0.99  --preprocessing_flag                    true
% 3.63/0.99  --time_out_prep_mult                    0.1
% 3.63/0.99  --splitting_mode                        input
% 3.63/0.99  --splitting_grd                         true
% 3.63/0.99  --splitting_cvd                         false
% 3.63/0.99  --splitting_cvd_svl                     false
% 3.63/0.99  --splitting_nvd                         32
% 3.63/0.99  --sub_typing                            true
% 3.63/0.99  --prep_gs_sim                           true
% 3.63/0.99  --prep_unflatten                        true
% 3.63/0.99  --prep_res_sim                          true
% 3.63/0.99  --prep_upred                            true
% 3.63/0.99  --prep_sem_filter                       exhaustive
% 3.63/0.99  --prep_sem_filter_out                   false
% 3.63/0.99  --pred_elim                             true
% 3.63/0.99  --res_sim_input                         true
% 3.63/0.99  --eq_ax_congr_red                       true
% 3.63/0.99  --pure_diseq_elim                       true
% 3.63/0.99  --brand_transform                       false
% 3.63/0.99  --non_eq_to_eq                          false
% 3.63/0.99  --prep_def_merge                        true
% 3.63/0.99  --prep_def_merge_prop_impl              false
% 3.63/0.99  --prep_def_merge_mbd                    true
% 3.63/0.99  --prep_def_merge_tr_red                 false
% 3.63/0.99  --prep_def_merge_tr_cl                  false
% 3.63/0.99  --smt_preprocessing                     true
% 3.63/0.99  --smt_ac_axioms                         fast
% 3.63/0.99  --preprocessed_out                      false
% 3.63/0.99  --preprocessed_stats                    false
% 3.63/0.99  
% 3.63/0.99  ------ Abstraction refinement Options
% 3.63/0.99  
% 3.63/0.99  --abstr_ref                             []
% 3.63/0.99  --abstr_ref_prep                        false
% 3.63/0.99  --abstr_ref_until_sat                   false
% 3.63/0.99  --abstr_ref_sig_restrict                funpre
% 3.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.99  --abstr_ref_under                       []
% 3.63/0.99  
% 3.63/0.99  ------ SAT Options
% 3.63/0.99  
% 3.63/0.99  --sat_mode                              false
% 3.63/0.99  --sat_fm_restart_options                ""
% 3.63/0.99  --sat_gr_def                            false
% 3.63/0.99  --sat_epr_types                         true
% 3.63/0.99  --sat_non_cyclic_types                  false
% 3.63/0.99  --sat_finite_models                     false
% 3.63/0.99  --sat_fm_lemmas                         false
% 3.63/0.99  --sat_fm_prep                           false
% 3.63/0.99  --sat_fm_uc_incr                        true
% 3.63/0.99  --sat_out_model                         small
% 3.63/0.99  --sat_out_clauses                       false
% 3.63/0.99  
% 3.63/0.99  ------ QBF Options
% 3.63/0.99  
% 3.63/0.99  --qbf_mode                              false
% 3.63/0.99  --qbf_elim_univ                         false
% 3.63/0.99  --qbf_dom_inst                          none
% 3.63/0.99  --qbf_dom_pre_inst                      false
% 3.63/0.99  --qbf_sk_in                             false
% 3.63/0.99  --qbf_pred_elim                         true
% 3.63/0.99  --qbf_split                             512
% 3.63/0.99  
% 3.63/0.99  ------ BMC1 Options
% 3.63/0.99  
% 3.63/0.99  --bmc1_incremental                      false
% 3.63/0.99  --bmc1_axioms                           reachable_all
% 3.63/0.99  --bmc1_min_bound                        0
% 3.63/0.99  --bmc1_max_bound                        -1
% 3.63/0.99  --bmc1_max_bound_default                -1
% 3.63/0.99  --bmc1_symbol_reachability              true
% 3.63/0.99  --bmc1_property_lemmas                  false
% 3.63/0.99  --bmc1_k_induction                      false
% 3.63/0.99  --bmc1_non_equiv_states                 false
% 3.63/0.99  --bmc1_deadlock                         false
% 3.63/0.99  --bmc1_ucm                              false
% 3.63/0.99  --bmc1_add_unsat_core                   none
% 3.63/0.99  --bmc1_unsat_core_children              false
% 3.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.99  --bmc1_out_stat                         full
% 3.63/0.99  --bmc1_ground_init                      false
% 3.63/0.99  --bmc1_pre_inst_next_state              false
% 3.63/0.99  --bmc1_pre_inst_state                   false
% 3.63/0.99  --bmc1_pre_inst_reach_state             false
% 3.63/0.99  --bmc1_out_unsat_core                   false
% 3.63/0.99  --bmc1_aig_witness_out                  false
% 3.63/0.99  --bmc1_verbose                          false
% 3.63/0.99  --bmc1_dump_clauses_tptp                false
% 3.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.99  --bmc1_dump_file                        -
% 3.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.99  --bmc1_ucm_extend_mode                  1
% 3.63/0.99  --bmc1_ucm_init_mode                    2
% 3.63/0.99  --bmc1_ucm_cone_mode                    none
% 3.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.99  --bmc1_ucm_relax_model                  4
% 3.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.99  --bmc1_ucm_layered_model                none
% 3.63/0.99  --bmc1_ucm_max_lemma_size               10
% 3.63/0.99  
% 3.63/0.99  ------ AIG Options
% 3.63/0.99  
% 3.63/0.99  --aig_mode                              false
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation Options
% 3.63/0.99  
% 3.63/0.99  --instantiation_flag                    true
% 3.63/0.99  --inst_sos_flag                         false
% 3.63/0.99  --inst_sos_phase                        true
% 3.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel_side                     none
% 3.63/0.99  --inst_solver_per_active                1400
% 3.63/0.99  --inst_solver_calls_frac                1.
% 3.63/0.99  --inst_passive_queue_type               priority_queues
% 3.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.99  --inst_passive_queues_freq              [25;2]
% 3.63/0.99  --inst_dismatching                      true
% 3.63/0.99  --inst_eager_unprocessed_to_passive     true
% 3.63/0.99  --inst_prop_sim_given                   true
% 3.63/0.99  --inst_prop_sim_new                     false
% 3.63/0.99  --inst_subs_new                         false
% 3.63/0.99  --inst_eq_res_simp                      false
% 3.63/0.99  --inst_subs_given                       false
% 3.63/0.99  --inst_orphan_elimination               true
% 3.63/0.99  --inst_learning_loop_flag               true
% 3.63/0.99  --inst_learning_start                   3000
% 3.63/0.99  --inst_learning_factor                  2
% 3.63/0.99  --inst_start_prop_sim_after_learn       3
% 3.63/0.99  --inst_sel_renew                        solver
% 3.63/0.99  --inst_lit_activity_flag                true
% 3.63/0.99  --inst_restr_to_given                   false
% 3.63/0.99  --inst_activity_threshold               500
% 3.63/0.99  --inst_out_proof                        true
% 3.63/0.99  
% 3.63/0.99  ------ Resolution Options
% 3.63/0.99  
% 3.63/0.99  --resolution_flag                       false
% 3.63/0.99  --res_lit_sel                           adaptive
% 3.63/0.99  --res_lit_sel_side                      none
% 3.63/0.99  --res_ordering                          kbo
% 3.63/0.99  --res_to_prop_solver                    active
% 3.63/0.99  --res_prop_simpl_new                    false
% 3.63/0.99  --res_prop_simpl_given                  true
% 3.63/0.99  --res_passive_queue_type                priority_queues
% 3.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.99  --res_passive_queues_freq               [15;5]
% 3.63/0.99  --res_forward_subs                      full
% 3.63/0.99  --res_backward_subs                     full
% 3.63/0.99  --res_forward_subs_resolution           true
% 3.63/0.99  --res_backward_subs_resolution          true
% 3.63/0.99  --res_orphan_elimination                true
% 3.63/0.99  --res_time_limit                        2.
% 3.63/0.99  --res_out_proof                         true
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Options
% 3.63/0.99  
% 3.63/0.99  --superposition_flag                    true
% 3.63/0.99  --sup_passive_queue_type                priority_queues
% 3.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.99  --demod_completeness_check              fast
% 3.63/0.99  --demod_use_ground                      true
% 3.63/0.99  --sup_to_prop_solver                    passive
% 3.63/0.99  --sup_prop_simpl_new                    true
% 3.63/0.99  --sup_prop_simpl_given                  true
% 3.63/0.99  --sup_fun_splitting                     false
% 3.63/0.99  --sup_smt_interval                      50000
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Simplification Setup
% 3.63/0.99  
% 3.63/0.99  --sup_indices_passive                   []
% 3.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_full_bw                           [BwDemod]
% 3.63/0.99  --sup_immed_triv                        [TrivRules]
% 3.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_immed_bw_main                     []
% 3.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  
% 3.63/0.99  ------ Combination Options
% 3.63/0.99  
% 3.63/0.99  --comb_res_mult                         3
% 3.63/0.99  --comb_sup_mult                         2
% 3.63/0.99  --comb_inst_mult                        10
% 3.63/0.99  
% 3.63/0.99  ------ Debug Options
% 3.63/0.99  
% 3.63/0.99  --dbg_backtrace                         false
% 3.63/0.99  --dbg_dump_prop_clauses                 false
% 3.63/0.99  --dbg_dump_prop_clauses_file            -
% 3.63/0.99  --dbg_out_stat                          false
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS status Theorem for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99   Resolution empty clause
% 3.63/0.99  
% 3.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  fof(f15,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f28,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(ennf_transformation,[],[f15])).
% 3.63/0.99  
% 3.63/0.99  fof(f29,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(flattening,[],[f28])).
% 3.63/0.99  
% 3.63/0.99  fof(f38,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(nnf_transformation,[],[f29])).
% 3.63/0.99  
% 3.63/0.99  fof(f60,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f16,conjecture,(
% 3.63/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f17,negated_conjecture,(
% 3.63/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.63/0.99    inference(negated_conjecture,[],[f16])).
% 3.63/0.99  
% 3.63/0.99  fof(f30,plain,(
% 3.63/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.63/0.99    inference(ennf_transformation,[],[f17])).
% 3.63/0.99  
% 3.63/0.99  fof(f31,plain,(
% 3.63/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.63/0.99    inference(flattening,[],[f30])).
% 3.63/0.99  
% 3.63/0.99  fof(f39,plain,(
% 3.63/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f40,plain,(
% 3.63/0.99    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f39])).
% 3.63/0.99  
% 3.63/0.99  fof(f67,plain,(
% 3.63/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f68,plain,(
% 3.63/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f12,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f24,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(ennf_transformation,[],[f12])).
% 3.63/0.99  
% 3.63/0.99  fof(f57,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f24])).
% 3.63/0.99  
% 3.63/0.99  fof(f11,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f18,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.63/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.63/0.99  
% 3.63/0.99  fof(f23,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(ennf_transformation,[],[f18])).
% 3.63/0.99  
% 3.63/0.99  fof(f56,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f9,axiom,(
% 3.63/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f22,plain,(
% 3.63/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.63/0.99    inference(ennf_transformation,[],[f9])).
% 3.63/0.99  
% 3.63/0.99  fof(f37,plain,(
% 3.63/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.63/0.99    inference(nnf_transformation,[],[f22])).
% 3.63/0.99  
% 3.63/0.99  fof(f53,plain,(
% 3.63/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f37])).
% 3.63/0.99  
% 3.63/0.99  fof(f13,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f25,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.99    inference(ennf_transformation,[],[f13])).
% 3.63/0.99  
% 3.63/0.99  fof(f58,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f25])).
% 3.63/0.99  
% 3.63/0.99  fof(f69,plain,(
% 3.63/0.99    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f14,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f26,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.63/0.99    inference(ennf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f27,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.63/0.99    inference(flattening,[],[f26])).
% 3.63/0.99  
% 3.63/0.99  fof(f59,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f27])).
% 3.63/0.99  
% 3.63/0.99  fof(f6,axiom,(
% 3.63/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f36,plain,(
% 3.63/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.63/0.99    inference(nnf_transformation,[],[f6])).
% 3.63/0.99  
% 3.63/0.99  fof(f50,plain,(
% 3.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f36])).
% 3.63/0.99  
% 3.63/0.99  fof(f8,axiom,(
% 3.63/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f21,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.63/0.99    inference(ennf_transformation,[],[f8])).
% 3.63/0.99  
% 3.63/0.99  fof(f52,plain,(
% 3.63/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f21])).
% 3.63/0.99  
% 3.63/0.99  fof(f51,plain,(
% 3.63/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f36])).
% 3.63/0.99  
% 3.63/0.99  fof(f10,axiom,(
% 3.63/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f55,plain,(
% 3.63/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f10])).
% 3.63/0.99  
% 3.63/0.99  fof(f62,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f71,plain,(
% 3.63/0.99    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f66,plain,(
% 3.63/0.99    v1_funct_1(sK3)),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f70,plain,(
% 3.63/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.63/0.99    inference(cnf_transformation,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f65,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f76,plain,(
% 3.63/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(equality_resolution,[],[f65])).
% 3.63/0.99  
% 3.63/0.99  fof(f77,plain,(
% 3.63/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.63/0.99    inference(equality_resolution,[],[f76])).
% 3.63/0.99  
% 3.63/0.99  fof(f5,axiom,(
% 3.63/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f49,plain,(
% 3.63/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f5])).
% 3.63/0.99  
% 3.63/0.99  fof(f1,axiom,(
% 3.63/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f32,plain,(
% 3.63/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.99    inference(nnf_transformation,[],[f1])).
% 3.63/0.99  
% 3.63/0.99  fof(f33,plain,(
% 3.63/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.99    inference(flattening,[],[f32])).
% 3.63/0.99  
% 3.63/0.99  fof(f43,plain,(
% 3.63/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f4,axiom,(
% 3.63/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f34,plain,(
% 3.63/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.63/0.99    inference(nnf_transformation,[],[f4])).
% 3.63/0.99  
% 3.63/0.99  fof(f35,plain,(
% 3.63/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.63/0.99    inference(flattening,[],[f34])).
% 3.63/0.99  
% 3.63/0.99  fof(f48,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.63/0.99    inference(cnf_transformation,[],[f35])).
% 3.63/0.99  
% 3.63/0.99  fof(f74,plain,(
% 3.63/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.63/0.99    inference(equality_resolution,[],[f48])).
% 3.63/0.99  
% 3.63/0.99  fof(f47,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.63/0.99    inference(cnf_transformation,[],[f35])).
% 3.63/0.99  
% 3.63/0.99  fof(f75,plain,(
% 3.63/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.63/0.99    inference(equality_resolution,[],[f47])).
% 3.63/0.99  
% 3.63/0.99  fof(f46,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f35])).
% 3.63/0.99  
% 3.63/0.99  fof(f64,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f78,plain,(
% 3.63/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.63/0.99    inference(equality_resolution,[],[f64])).
% 3.63/0.99  
% 3.63/0.99  fof(f61,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f80,plain,(
% 3.63/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.63/0.99    inference(equality_resolution,[],[f61])).
% 3.63/0.99  
% 3.63/0.99  fof(f63,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f38])).
% 3.63/0.99  
% 3.63/0.99  fof(f79,plain,(
% 3.63/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.63/0.99    inference(equality_resolution,[],[f63])).
% 3.63/0.99  
% 3.63/0.99  cnf(c_24,plain,
% 3.63/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.99      | k1_xboole_0 = X2 ),
% 3.63/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_29,negated_conjecture,
% 3.63/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_472,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.99      | sK1 != X2
% 3.63/0.99      | sK0 != X1
% 3.63/0.99      | sK3 != X0
% 3.63/0.99      | k1_xboole_0 = X2 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_473,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.63/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.63/0.99      | k1_xboole_0 = sK1 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_472]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_28,negated_conjecture,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.63/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_475,plain,
% 3.63/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_473,c_28]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1234,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_16,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1238,plain,
% 3.63/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.63/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3104,plain,
% 3.63/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1234,c_1238]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3190,plain,
% 3.63/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_475,c_3104]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_15,plain,
% 3.63/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.63/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13,plain,
% 3.63/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_360,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.63/0.99      | ~ v1_relat_1(X0) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_15,c_13]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1232,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1605,plain,
% 3.63/0.99      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1234,c_1232]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1237,plain,
% 3.63/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.63/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2301,plain,
% 3.63/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1234,c_1237]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_27,negated_conjecture,
% 3.63/0.99      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 3.63/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1235,plain,
% 3.63/0.99      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2410,plain,
% 3.63/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_2301,c_1235]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_18,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.63/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.63/0.99      | ~ v1_relat_1(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1236,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.63/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3103,plain,
% 3.63/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.63/0.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.63/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1236,c_1238]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_11852,plain,
% 3.63/0.99      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.63/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2410,c_3103]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_10,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1240,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.63/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2141,plain,
% 3.63/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1234,c_1240]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_11,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_9,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_216,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.63/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_217,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_216]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_270,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.63/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_217]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1233,plain,
% 3.63/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.63/0.99      | v1_relat_1(X1) != iProver_top
% 3.63/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2326,plain,
% 3.63/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.63/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2141,c_1233]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_14,plain,
% 3.63/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.63/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1239,plain,
% 3.63/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2503,plain,
% 3.63/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2326,c_1239]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12274,plain,
% 3.63/0.99      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.63/0.99      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_11852,c_2503]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12275,plain,
% 3.63/0.99      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.63/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_12274]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12285,plain,
% 3.63/0.99      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3)
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1605,c_12275]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12456,plain,
% 3.63/0.99      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_12285,c_2503]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_22,plain,
% 3.63/0.99      ( v1_funct_2(X0,X1,X2)
% 3.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.63/0.99      | k1_xboole_0 = X2 ),
% 3.63/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_25,negated_conjecture,
% 3.63/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ v1_funct_1(sK3) ),
% 3.63/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_30,negated_conjecture,
% 3.63/0.99      ( v1_funct_1(sK3) ),
% 3.63/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_155,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 3.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_25,c_30]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_156,negated_conjecture,
% 3.63/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_155]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_459,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.63/0.99      | sK2 != X2
% 3.63/0.99      | sK0 != X1
% 3.63/0.99      | sK3 != X0
% 3.63/0.99      | k1_xboole_0 = X2 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_156]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_460,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | k1_relset_1(sK0,sK2,sK3) != sK0
% 3.63/0.99      | k1_xboole_0 = sK2 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1227,plain,
% 3.63/0.99      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 3.63/0.99      | k1_xboole_0 = sK2
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12459,plain,
% 3.63/0.99      ( k1_relat_1(sK3) != sK0
% 3.63/0.99      | sK2 = k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12456,c_1227]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1769,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.63/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.63/0.99      | ~ v1_relat_1(sK3) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1770,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.63/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12462,plain,
% 3.63/0.99      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) != sK0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_12459,c_1605,c_1770,c_2410,c_2503]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12463,plain,
% 3.63/0.99      ( k1_relat_1(sK3) != sK0 | sK2 = k1_xboole_0 ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_12462]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12466,plain,
% 3.63/0.99      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3190,c_12463]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_26,negated_conjecture,
% 3.63/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12601,plain,
% 3.63/0.99      ( sK2 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_12466,c_26]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19,plain,
% 3.63/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.63/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.63/0.99      | k1_xboole_0 = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_387,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.63/0.99      | sK2 != k1_xboole_0
% 3.63/0.99      | sK0 != X0
% 3.63/0.99      | sK3 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_156]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_388,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.63/0.99      | sK2 != k1_xboole_0
% 3.63/0.99      | sK3 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = sK0 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_387]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_8,plain,
% 3.63/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.63/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_400,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | sK2 != k1_xboole_0
% 3.63/0.99      | sK3 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = sK0 ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_388,c_8]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1231,plain,
% 3.63/0.99      ( sK2 != k1_xboole_0
% 3.63/0.99      | sK3 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = sK0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12643,plain,
% 3.63/0.99      ( sK0 = k1_xboole_0
% 3.63/0.99      | sK3 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_12601,c_1231]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_0,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1427,plain,
% 3.63/0.99      ( ~ r1_tarski(sK0,k1_xboole_0)
% 3.63/0.99      | ~ r1_tarski(k1_xboole_0,sK0)
% 3.63/0.99      | sK0 = k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1628,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1630,plain,
% 3.63/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 3.63/0.99      | r1_tarski(k1_xboole_0,sK0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1628]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1997,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1999,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.99      | r1_tarski(sK3,k1_xboole_0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2117,plain,
% 3.63/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5,plain,
% 3.63/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2654,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.63/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_5,c_1236]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3419,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.63/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1605,c_2654]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3629,plain,
% 3.63/0.99      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3419,c_2503]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3630,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.63/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_3629]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3631,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.99      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
% 3.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3630]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_6,plain,
% 3.63/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1241,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.63/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2149,plain,
% 3.63/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1241,c_1232]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3714,plain,
% 3.63/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.63/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 3.63/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_6,c_2149]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3734,plain,
% 3.63/0.99      ( sK1 = k1_xboole_0
% 3.63/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 3.63/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.63/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3190,c_3714]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_76,plain,
% 3.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.63/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_78,plain,
% 3.63/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.63/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_76]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_82,plain,
% 3.63/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_84,plain,
% 3.63/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_82]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_7,plain,
% 3.63/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = X0
% 3.63/0.99      | k1_xboole_0 = X1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_85,plain,
% 3.63/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_86,plain,
% 3.63/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_726,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.63/0.99      theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1498,plain,
% 3.63/0.99      ( ~ r1_tarski(X0,X1)
% 3.63/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.63/0.99      | sK0 != X0
% 3.63/0.99      | k1_xboole_0 != X1 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1499,plain,
% 3.63/0.99      ( sK0 != X0
% 3.63/0.99      | k1_xboole_0 != X1
% 3.63/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.63/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1501,plain,
% 3.63/0.99      ( sK0 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != k1_xboole_0
% 3.63/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 3.63/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1499]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_20,plain,
% 3.63/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.63/0.99      | k1_xboole_0 = X1
% 3.63/0.99      | k1_xboole_0 = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_410,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.63/0.99      | sK1 != k1_xboole_0
% 3.63/0.99      | sK0 != X1
% 3.63/0.99      | sK3 != X0
% 3.63/0.99      | k1_xboole_0 = X0
% 3.63/0.99      | k1_xboole_0 = X1 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_411,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.63/0.99      | sK1 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = sK0
% 3.63/0.99      | k1_xboole_0 = sK3 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1230,plain,
% 3.63/0.99      ( sK1 != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = sK0
% 3.63/0.99      | k1_xboole_0 = sK3
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1326,plain,
% 3.63/0.99      ( sK1 != k1_xboole_0
% 3.63/0.99      | sK0 = k1_xboole_0
% 3.63/0.99      | sK3 = k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_1230,c_5]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_725,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1443,plain,
% 3.63/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1515,plain,
% 3.63/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1443]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_724,plain,( X0 = X0 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1516,plain,
% 3.63/0.99      ( sK0 = sK0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_724]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1619,plain,
% 3.63/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1620,plain,
% 3.63/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1619]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1779,plain,
% 3.63/0.99      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1326,c_26,c_85,c_86,c_1515,c_1516,c_1620]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4072,plain,
% 3.63/0.99      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.63/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_3734,c_78,c_84,c_85,c_86,c_1501,c_1779,c_2503]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4073,plain,
% 3.63/0.99      ( r1_tarski(sK0,k1_xboole_0) = iProver_top
% 3.63/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_4072]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4074,plain,
% 3.63/0.99      ( r1_tarski(sK0,k1_xboole_0) | ~ r1_tarski(sK3,k1_xboole_0) ),
% 3.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4073]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12641,plain,
% 3.63/0.99      ( sK0 = k1_xboole_0
% 3.63/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_12601,c_2410]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12680,plain,
% 3.63/0.99      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) | sK0 = k1_xboole_0 ),
% 3.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_12641]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12855,plain,
% 3.63/0.99      ( sK0 = k1_xboole_0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_12643,c_1427,c_1630,c_1999,c_2117,c_3631,c_4074,c_12680]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12859,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12855,c_12456]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12913,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12855,c_3104]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_23,plain,
% 3.63/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_446,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.63/0.99      | sK1 != X1
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | sK3 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_447,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1228,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1319,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_1228,c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12921,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12855,c_1319]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12938,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(equality_resolution_simp,[status(thm)],[c_12921]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12924,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12855,c_1234]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12927,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12924,c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12941,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_12938,c_12927]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12964,plain,
% 3.63/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.63/0.99      inference(light_normalisation,[status(thm)],[c_12913,c_12941]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13140,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
% 3.63/0.99      inference(light_normalisation,[status(thm)],[c_12859,c_12964]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_21,plain,
% 3.63/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_430,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.63/0.99      | sK2 != X1
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | sK3 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_156]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_431,plain,
% 3.63/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.63/0.99      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1229,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1357,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | sK0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_1229,c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12918,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12855,c_1357]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12947,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(equality_resolution_simp,[status(thm)],[c_12918]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12951,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_12947,c_12927]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12952,plain,
% 3.63/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_12951,c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13142,plain,
% 3.63/0.99      ( k1_xboole_0 != k1_xboole_0
% 3.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(demodulation,[status(thm)],[c_13140,c_12952]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13144,plain,
% 3.63/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.99      inference(equality_resolution_simp,[status(thm)],[c_13142]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13146,plain,
% 3.63/0.99      ( $false ),
% 3.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_13144,c_12927]) ).
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  ------                               Statistics
% 3.63/0.99  
% 3.63/0.99  ------ General
% 3.63/0.99  
% 3.63/0.99  abstr_ref_over_cycles:                  0
% 3.63/0.99  abstr_ref_under_cycles:                 0
% 3.63/0.99  gc_basic_clause_elim:                   0
% 3.63/0.99  forced_gc_time:                         0
% 3.63/0.99  parsing_time:                           0.008
% 3.63/0.99  unif_index_cands_time:                  0.
% 3.63/0.99  unif_index_add_time:                    0.
% 3.63/0.99  orderings_time:                         0.
% 3.63/0.99  out_proof_time:                         0.011
% 3.63/0.99  total_time:                             0.327
% 3.63/0.99  num_of_symbols:                         48
% 3.63/0.99  num_of_terms:                           7978
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing
% 3.63/0.99  
% 3.63/0.99  num_of_splits:                          0
% 3.63/0.99  num_of_split_atoms:                     0
% 3.63/0.99  num_of_reused_defs:                     0
% 3.63/0.99  num_eq_ax_congr_red:                    10
% 3.63/0.99  num_of_sem_filtered_clauses:            2
% 3.63/0.99  num_of_subtypes:                        0
% 3.63/0.99  monotx_restored_types:                  0
% 3.63/0.99  sat_num_of_epr_types:                   0
% 3.63/0.99  sat_num_of_non_cyclic_types:            0
% 3.63/0.99  sat_guarded_non_collapsed_types:        0
% 3.63/0.99  num_pure_diseq_elim:                    0
% 3.63/0.99  simp_replaced_by:                       0
% 3.63/0.99  res_preprocessed:                       127
% 3.63/0.99  prep_upred:                             0
% 3.63/0.99  prep_unflattend:                        33
% 3.63/0.99  smt_new_axioms:                         0
% 3.63/0.99  pred_elim_cands:                        3
% 3.63/0.99  pred_elim:                              2
% 3.63/0.99  pred_elim_cl:                           3
% 3.63/0.99  pred_elim_cycles:                       4
% 3.63/0.99  merged_defs:                            8
% 3.63/0.99  merged_defs_ncl:                        0
% 3.63/0.99  bin_hyper_res:                          9
% 3.63/0.99  prep_cycles:                            4
% 3.63/0.99  pred_elim_time:                         0.004
% 3.63/0.99  splitting_time:                         0.
% 3.63/0.99  sem_filter_time:                        0.
% 3.63/0.99  monotx_time:                            0.001
% 3.63/0.99  subtype_inf_time:                       0.
% 3.63/0.99  
% 3.63/0.99  ------ Problem properties
% 3.63/0.99  
% 3.63/0.99  clauses:                                26
% 3.63/0.99  conjectures:                            3
% 3.63/0.99  epr:                                    6
% 3.63/0.99  horn:                                   23
% 3.63/0.99  ground:                                 10
% 3.63/0.99  unary:                                  8
% 3.63/0.99  binary:                                 8
% 3.63/0.99  lits:                                   58
% 3.63/0.99  lits_eq:                                26
% 3.63/0.99  fd_pure:                                0
% 3.63/0.99  fd_pseudo:                              0
% 3.63/0.99  fd_cond:                                2
% 3.63/0.99  fd_pseudo_cond:                         1
% 3.63/0.99  ac_symbols:                             0
% 3.63/0.99  
% 3.63/0.99  ------ Propositional Solver
% 3.63/0.99  
% 3.63/0.99  prop_solver_calls:                      28
% 3.63/0.99  prop_fast_solver_calls:                 1160
% 3.63/0.99  smt_solver_calls:                       0
% 3.63/0.99  smt_fast_solver_calls:                  0
% 3.63/0.99  prop_num_of_clauses:                    4075
% 3.63/0.99  prop_preprocess_simplified:             9246
% 3.63/0.99  prop_fo_subsumed:                       46
% 3.63/0.99  prop_solver_time:                       0.
% 3.63/0.99  smt_solver_time:                        0.
% 3.63/0.99  smt_fast_solver_time:                   0.
% 3.63/0.99  prop_fast_solver_time:                  0.
% 3.63/0.99  prop_unsat_core_time:                   0.
% 3.63/0.99  
% 3.63/0.99  ------ QBF
% 3.63/0.99  
% 3.63/0.99  qbf_q_res:                              0
% 3.63/0.99  qbf_num_tautologies:                    0
% 3.63/0.99  qbf_prep_cycles:                        0
% 3.63/0.99  
% 3.63/0.99  ------ BMC1
% 3.63/0.99  
% 3.63/0.99  bmc1_current_bound:                     -1
% 3.63/0.99  bmc1_last_solved_bound:                 -1
% 3.63/0.99  bmc1_unsat_core_size:                   -1
% 3.63/0.99  bmc1_unsat_core_parents_size:           -1
% 3.63/0.99  bmc1_merge_next_fun:                    0
% 3.63/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation
% 3.63/0.99  
% 3.63/0.99  inst_num_of_clauses:                    1138
% 3.63/0.99  inst_num_in_passive:                    21
% 3.63/0.99  inst_num_in_active:                     617
% 3.63/0.99  inst_num_in_unprocessed:                500
% 3.63/0.99  inst_num_of_loops:                      760
% 3.63/0.99  inst_num_of_learning_restarts:          0
% 3.63/0.99  inst_num_moves_active_passive:          141
% 3.63/0.99  inst_lit_activity:                      0
% 3.63/0.99  inst_lit_activity_moves:                0
% 3.63/0.99  inst_num_tautologies:                   0
% 3.63/0.99  inst_num_prop_implied:                  0
% 3.63/0.99  inst_num_existing_simplified:           0
% 3.63/0.99  inst_num_eq_res_simplified:             0
% 3.63/0.99  inst_num_child_elim:                    0
% 3.63/0.99  inst_num_of_dismatching_blockings:      558
% 3.63/0.99  inst_num_of_non_proper_insts:           1694
% 3.63/0.99  inst_num_of_duplicates:                 0
% 3.63/0.99  inst_inst_num_from_inst_to_res:         0
% 3.63/0.99  inst_dismatching_checking_time:         0.
% 3.63/0.99  
% 3.63/0.99  ------ Resolution
% 3.63/0.99  
% 3.63/0.99  res_num_of_clauses:                     0
% 3.63/0.99  res_num_in_passive:                     0
% 3.63/0.99  res_num_in_active:                      0
% 3.63/0.99  res_num_of_loops:                       131
% 3.63/0.99  res_forward_subset_subsumed:            105
% 3.63/0.99  res_backward_subset_subsumed:           0
% 3.63/0.99  res_forward_subsumed:                   0
% 3.63/0.99  res_backward_subsumed:                  0
% 3.63/0.99  res_forward_subsumption_resolution:     1
% 3.63/0.99  res_backward_subsumption_resolution:    0
% 3.63/1.00  res_clause_to_clause_subsumption:       1743
% 3.63/1.00  res_orphan_elimination:                 0
% 3.63/1.00  res_tautology_del:                      102
% 3.63/1.00  res_num_eq_res_simplified:              1
% 3.63/1.00  res_num_sel_changes:                    0
% 3.63/1.00  res_moves_from_active_to_pass:          0
% 3.63/1.00  
% 3.63/1.00  ------ Superposition
% 3.63/1.00  
% 3.63/1.00  sup_time_total:                         0.
% 3.63/1.00  sup_time_generating:                    0.
% 3.63/1.00  sup_time_sim_full:                      0.
% 3.63/1.00  sup_time_sim_immed:                     0.
% 3.63/1.00  
% 3.63/1.00  sup_num_of_clauses:                     185
% 3.63/1.00  sup_num_in_active:                      76
% 3.63/1.00  sup_num_in_passive:                     109
% 3.63/1.00  sup_num_of_loops:                       150
% 3.63/1.00  sup_fw_superposition:                   310
% 3.63/1.00  sup_bw_superposition:                   159
% 3.63/1.00  sup_immediate_simplified:               117
% 3.63/1.00  sup_given_eliminated:                   2
% 3.63/1.00  comparisons_done:                       0
% 3.63/1.00  comparisons_avoided:                    78
% 3.63/1.00  
% 3.63/1.00  ------ Simplifications
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  sim_fw_subset_subsumed:                 24
% 3.63/1.00  sim_bw_subset_subsumed:                 3
% 3.63/1.00  sim_fw_subsumed:                        58
% 3.63/1.00  sim_bw_subsumed:                        22
% 3.63/1.00  sim_fw_subsumption_res:                 8
% 3.63/1.00  sim_bw_subsumption_res:                 0
% 3.63/1.00  sim_tautology_del:                      17
% 3.63/1.00  sim_eq_tautology_del:                   58
% 3.63/1.00  sim_eq_res_simp:                        3
% 3.63/1.00  sim_fw_demodulated:                     51
% 3.63/1.00  sim_bw_demodulated:                     75
% 3.63/1.00  sim_light_normalised:                   76
% 3.63/1.00  sim_joinable_taut:                      0
% 3.63/1.00  sim_joinable_simp:                      0
% 3.63/1.00  sim_ac_normalised:                      0
% 3.63/1.00  sim_smt_subsumption:                    0
% 3.63/1.00  
%------------------------------------------------------------------------------
