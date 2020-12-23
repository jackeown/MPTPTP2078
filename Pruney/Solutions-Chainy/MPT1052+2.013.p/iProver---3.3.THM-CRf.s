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
% DateTime   : Thu Dec  3 12:08:56 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  167 (2862 expanded)
%              Number of clauses        :   94 ( 927 expanded)
%              Number of leaves         :   22 ( 548 expanded)
%              Depth                    :   30
%              Number of atoms          :  446 (8837 expanded)
%              Number of equality atoms :  252 (3727 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
        | k1_relat_1(sK3) != sK1 )
      & r2_hidden(sK3,k1_funct_2(sK1,sK2))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
      | k1_relat_1(sK3) != sK1 )
    & r2_hidden(sK3,k1_funct_2(sK1,sK2))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f43])).

fof(f77,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f75])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f42,plain,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1884,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3384,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1886])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3535,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3384,c_1892])).

cnf(c_14,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1890,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4303,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1890])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_72,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5916,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_72])).

cnf(c_5917,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5916])).

cnf(c_5927,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3535,c_5917])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_29,c_26])).

cnf(c_427,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_28,c_26])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_29])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_29,c_427])).

cnf(c_1882,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_3166,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1884,c_1882])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1888,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3536,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3384,c_1888])).

cnf(c_3616,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3166,c_3536])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1885,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3803,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_1885])).

cnf(c_3804,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3803])).

cnf(c_5952,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5927])).

cnf(c_5954,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5927,c_32,c_3804,c_5952])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1896,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3608,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3535,c_1896])).

cnf(c_5963,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | sK2 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5954,c_3608])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6001,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5963,c_9])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2374,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2377,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_6787,plain,
    ( sK2 = k1_xboole_0
    | k2_zfmisc_1(sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6001,c_2377])).

cnf(c_6788,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6787])).

cnf(c_6791,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5954,c_6788])).

cnf(c_6837,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6791,c_9])).

cnf(c_7070,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6837,c_1884])).

cnf(c_2520,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2521,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_2523,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_7065,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6837,c_3535])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7087,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7065,c_8])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_85,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_1338,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2928,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_2929,plain,
    ( X0 != X1
    | sK3 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2928])).

cnf(c_2931,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_7114,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7087,c_81,c_82,c_85,c_2931])).

cnf(c_7231,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7070,c_81,c_82,c_85,c_2377,c_2523,c_2931,c_7087])).

cnf(c_7259,plain,
    ( k1_relat_1(k1_xboole_0) != sK1
    | r1_tarski(k2_relat_1(k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7231,c_1885])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7266,plain,
    ( sK1 != k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7259,c_18,c_19])).

cnf(c_2483,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2486,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_7498,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7266,c_2486])).

cnf(c_7501,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5954,c_7498])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1887,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1899,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2581,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1899])).

cnf(c_3398,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_2581])).

cnf(c_7684,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7501,c_3398])).

cnf(c_1335,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3438,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_6874,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_6875,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_6874])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3483,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3484,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3483])).

cnf(c_1334,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3445,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7684,c_7266,c_6875,c_3484,c_3445,c_2486,c_94])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n024.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 14:59:21 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 2.71/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/0.91  
% 2.71/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/0.91  
% 2.71/0.91  ------  iProver source info
% 2.71/0.91  
% 2.71/0.91  git: date: 2020-06-30 10:37:57 +0100
% 2.71/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/0.91  git: non_committed_changes: false
% 2.71/0.91  git: last_make_outside_of_git: false
% 2.71/0.91  
% 2.71/0.91  ------ 
% 2.71/0.91  
% 2.71/0.91  ------ Input Options
% 2.71/0.91  
% 2.71/0.91  --out_options                           all
% 2.71/0.91  --tptp_safe_out                         true
% 2.71/0.91  --problem_path                          ""
% 2.71/0.91  --include_path                          ""
% 2.71/0.91  --clausifier                            res/vclausify_rel
% 2.71/0.91  --clausifier_options                    --mode clausify
% 2.71/0.91  --stdin                                 false
% 2.71/0.91  --stats_out                             all
% 2.71/0.91  
% 2.71/0.91  ------ General Options
% 2.71/0.91  
% 2.71/0.91  --fof                                   false
% 2.71/0.91  --time_out_real                         305.
% 2.71/0.91  --time_out_virtual                      -1.
% 2.71/0.91  --symbol_type_check                     false
% 2.71/0.91  --clausify_out                          false
% 2.71/0.91  --sig_cnt_out                           false
% 2.71/0.91  --trig_cnt_out                          false
% 2.71/0.91  --trig_cnt_out_tolerance                1.
% 2.71/0.91  --trig_cnt_out_sk_spl                   false
% 2.71/0.91  --abstr_cl_out                          false
% 2.71/0.91  
% 2.71/0.91  ------ Global Options
% 2.71/0.91  
% 2.71/0.91  --schedule                              default
% 2.71/0.91  --add_important_lit                     false
% 2.71/0.91  --prop_solver_per_cl                    1000
% 2.71/0.91  --min_unsat_core                        false
% 2.71/0.91  --soft_assumptions                      false
% 2.71/0.91  --soft_lemma_size                       3
% 2.71/0.91  --prop_impl_unit_size                   0
% 2.71/0.91  --prop_impl_unit                        []
% 2.71/0.91  --share_sel_clauses                     true
% 2.71/0.91  --reset_solvers                         false
% 2.71/0.91  --bc_imp_inh                            [conj_cone]
% 2.71/0.91  --conj_cone_tolerance                   3.
% 2.71/0.91  --extra_neg_conj                        none
% 2.71/0.91  --large_theory_mode                     true
% 2.71/0.91  --prolific_symb_bound                   200
% 2.71/0.91  --lt_threshold                          2000
% 2.71/0.91  --clause_weak_htbl                      true
% 2.71/0.91  --gc_record_bc_elim                     false
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing Options
% 2.71/0.91  
% 2.71/0.91  --preprocessing_flag                    true
% 2.71/0.91  --time_out_prep_mult                    0.1
% 2.71/0.91  --splitting_mode                        input
% 2.71/0.91  --splitting_grd                         true
% 2.71/0.91  --splitting_cvd                         false
% 2.71/0.91  --splitting_cvd_svl                     false
% 2.71/0.91  --splitting_nvd                         32
% 2.71/0.91  --sub_typing                            true
% 2.71/0.91  --prep_gs_sim                           true
% 2.71/0.91  --prep_unflatten                        true
% 2.71/0.91  --prep_res_sim                          true
% 2.71/0.91  --prep_upred                            true
% 2.71/0.91  --prep_sem_filter                       exhaustive
% 2.71/0.91  --prep_sem_filter_out                   false
% 2.71/0.91  --pred_elim                             true
% 2.71/0.91  --res_sim_input                         true
% 2.71/0.91  --eq_ax_congr_red                       true
% 2.71/0.91  --pure_diseq_elim                       true
% 2.71/0.91  --brand_transform                       false
% 2.71/0.91  --non_eq_to_eq                          false
% 2.71/0.91  --prep_def_merge                        true
% 2.71/0.91  --prep_def_merge_prop_impl              false
% 2.71/0.91  --prep_def_merge_mbd                    true
% 2.71/0.91  --prep_def_merge_tr_red                 false
% 2.71/0.91  --prep_def_merge_tr_cl                  false
% 2.71/0.91  --smt_preprocessing                     true
% 2.71/0.91  --smt_ac_axioms                         fast
% 2.71/0.91  --preprocessed_out                      false
% 2.71/0.91  --preprocessed_stats                    false
% 2.71/0.91  
% 2.71/0.91  ------ Abstraction refinement Options
% 2.71/0.91  
% 2.71/0.91  --abstr_ref                             []
% 2.71/0.91  --abstr_ref_prep                        false
% 2.71/0.91  --abstr_ref_until_sat                   false
% 2.71/0.91  --abstr_ref_sig_restrict                funpre
% 2.71/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.91  --abstr_ref_under                       []
% 2.71/0.91  
% 2.71/0.91  ------ SAT Options
% 2.71/0.91  
% 2.71/0.91  --sat_mode                              false
% 2.71/0.91  --sat_fm_restart_options                ""
% 2.71/0.91  --sat_gr_def                            false
% 2.71/0.91  --sat_epr_types                         true
% 2.71/0.91  --sat_non_cyclic_types                  false
% 2.71/0.91  --sat_finite_models                     false
% 2.71/0.91  --sat_fm_lemmas                         false
% 2.71/0.91  --sat_fm_prep                           false
% 2.71/0.91  --sat_fm_uc_incr                        true
% 2.71/0.91  --sat_out_model                         small
% 2.71/0.91  --sat_out_clauses                       false
% 2.71/0.91  
% 2.71/0.91  ------ QBF Options
% 2.71/0.91  
% 2.71/0.91  --qbf_mode                              false
% 2.71/0.91  --qbf_elim_univ                         false
% 2.71/0.91  --qbf_dom_inst                          none
% 2.71/0.91  --qbf_dom_pre_inst                      false
% 2.71/0.91  --qbf_sk_in                             false
% 2.71/0.91  --qbf_pred_elim                         true
% 2.71/0.91  --qbf_split                             512
% 2.71/0.91  
% 2.71/0.91  ------ BMC1 Options
% 2.71/0.91  
% 2.71/0.91  --bmc1_incremental                      false
% 2.71/0.91  --bmc1_axioms                           reachable_all
% 2.71/0.91  --bmc1_min_bound                        0
% 2.71/0.91  --bmc1_max_bound                        -1
% 2.71/0.91  --bmc1_max_bound_default                -1
% 2.71/0.91  --bmc1_symbol_reachability              true
% 2.71/0.91  --bmc1_property_lemmas                  false
% 2.71/0.91  --bmc1_k_induction                      false
% 2.71/0.91  --bmc1_non_equiv_states                 false
% 2.71/0.91  --bmc1_deadlock                         false
% 2.71/0.91  --bmc1_ucm                              false
% 2.71/0.91  --bmc1_add_unsat_core                   none
% 2.71/0.91  --bmc1_unsat_core_children              false
% 2.71/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.91  --bmc1_out_stat                         full
% 2.71/0.91  --bmc1_ground_init                      false
% 2.71/0.91  --bmc1_pre_inst_next_state              false
% 2.71/0.91  --bmc1_pre_inst_state                   false
% 2.71/0.91  --bmc1_pre_inst_reach_state             false
% 2.71/0.91  --bmc1_out_unsat_core                   false
% 2.71/0.91  --bmc1_aig_witness_out                  false
% 2.71/0.91  --bmc1_verbose                          false
% 2.71/0.91  --bmc1_dump_clauses_tptp                false
% 2.71/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.91  --bmc1_dump_file                        -
% 2.71/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.91  --bmc1_ucm_extend_mode                  1
% 2.71/0.91  --bmc1_ucm_init_mode                    2
% 2.71/0.91  --bmc1_ucm_cone_mode                    none
% 2.71/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.91  --bmc1_ucm_relax_model                  4
% 2.71/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.91  --bmc1_ucm_layered_model                none
% 2.71/0.91  --bmc1_ucm_max_lemma_size               10
% 2.71/0.91  
% 2.71/0.91  ------ AIG Options
% 2.71/0.91  
% 2.71/0.91  --aig_mode                              false
% 2.71/0.91  
% 2.71/0.91  ------ Instantiation Options
% 2.71/0.91  
% 2.71/0.91  --instantiation_flag                    true
% 2.71/0.91  --inst_sos_flag                         false
% 2.71/0.91  --inst_sos_phase                        true
% 2.71/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.91  --inst_lit_sel_side                     num_symb
% 2.71/0.91  --inst_solver_per_active                1400
% 2.71/0.91  --inst_solver_calls_frac                1.
% 2.71/0.91  --inst_passive_queue_type               priority_queues
% 2.71/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.91  --inst_passive_queues_freq              [25;2]
% 2.71/0.91  --inst_dismatching                      true
% 2.71/0.91  --inst_eager_unprocessed_to_passive     true
% 2.71/0.91  --inst_prop_sim_given                   true
% 2.71/0.91  --inst_prop_sim_new                     false
% 2.71/0.91  --inst_subs_new                         false
% 2.71/0.91  --inst_eq_res_simp                      false
% 2.71/0.91  --inst_subs_given                       false
% 2.71/0.91  --inst_orphan_elimination               true
% 2.71/0.91  --inst_learning_loop_flag               true
% 2.71/0.91  --inst_learning_start                   3000
% 2.71/0.91  --inst_learning_factor                  2
% 2.71/0.91  --inst_start_prop_sim_after_learn       3
% 2.71/0.91  --inst_sel_renew                        solver
% 2.71/0.91  --inst_lit_activity_flag                true
% 2.71/0.91  --inst_restr_to_given                   false
% 2.71/0.91  --inst_activity_threshold               500
% 2.71/0.91  --inst_out_proof                        true
% 2.71/0.91  
% 2.71/0.91  ------ Resolution Options
% 2.71/0.91  
% 2.71/0.91  --resolution_flag                       true
% 2.71/0.91  --res_lit_sel                           adaptive
% 2.71/0.91  --res_lit_sel_side                      none
% 2.71/0.91  --res_ordering                          kbo
% 2.71/0.91  --res_to_prop_solver                    active
% 2.71/0.91  --res_prop_simpl_new                    false
% 2.71/0.91  --res_prop_simpl_given                  true
% 2.71/0.91  --res_passive_queue_type                priority_queues
% 2.71/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.91  --res_passive_queues_freq               [15;5]
% 2.71/0.91  --res_forward_subs                      full
% 2.71/0.91  --res_backward_subs                     full
% 2.71/0.91  --res_forward_subs_resolution           true
% 2.71/0.91  --res_backward_subs_resolution          true
% 2.71/0.91  --res_orphan_elimination                true
% 2.71/0.91  --res_time_limit                        2.
% 2.71/0.91  --res_out_proof                         true
% 2.71/0.91  
% 2.71/0.91  ------ Superposition Options
% 2.71/0.91  
% 2.71/0.91  --superposition_flag                    true
% 2.71/0.91  --sup_passive_queue_type                priority_queues
% 2.71/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.91  --demod_completeness_check              fast
% 2.71/0.91  --demod_use_ground                      true
% 2.71/0.91  --sup_to_prop_solver                    passive
% 2.71/0.91  --sup_prop_simpl_new                    true
% 2.71/0.91  --sup_prop_simpl_given                  true
% 2.71/0.91  --sup_fun_splitting                     false
% 2.71/0.91  --sup_smt_interval                      50000
% 2.71/0.91  
% 2.71/0.91  ------ Superposition Simplification Setup
% 2.71/0.91  
% 2.71/0.91  --sup_indices_passive                   []
% 2.71/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_full_bw                           [BwDemod]
% 2.71/0.91  --sup_immed_triv                        [TrivRules]
% 2.71/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_immed_bw_main                     []
% 2.71/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.91  
% 2.71/0.91  ------ Combination Options
% 2.71/0.91  
% 2.71/0.91  --comb_res_mult                         3
% 2.71/0.91  --comb_sup_mult                         2
% 2.71/0.91  --comb_inst_mult                        10
% 2.71/0.91  
% 2.71/0.91  ------ Debug Options
% 2.71/0.91  
% 2.71/0.91  --dbg_backtrace                         false
% 2.71/0.91  --dbg_dump_prop_clauses                 false
% 2.71/0.91  --dbg_dump_prop_clauses_file            -
% 2.71/0.91  --dbg_out_stat                          false
% 2.71/0.91  ------ Parsing...
% 2.71/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/0.91  ------ Proving...
% 2.71/0.91  ------ Problem Properties 
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  clauses                                 28
% 2.71/0.91  conjectures                             3
% 2.71/0.91  EPR                                     7
% 2.71/0.91  Horn                                    21
% 2.71/0.91  unary                                   10
% 2.71/0.91  binary                                  9
% 2.71/0.91  lits                                    57
% 2.71/0.91  lits eq                                 22
% 2.71/0.91  fd_pure                                 0
% 2.71/0.91  fd_pseudo                               0
% 2.71/0.91  fd_cond                                 3
% 2.71/0.91  fd_pseudo_cond                          1
% 2.71/0.91  AC symbols                              0
% 2.71/0.91  
% 2.71/0.91  ------ Schedule dynamic 5 is on 
% 2.71/0.91  
% 2.71/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  ------ 
% 2.71/0.91  Current options:
% 2.71/0.91  ------ 
% 2.71/0.91  
% 2.71/0.91  ------ Input Options
% 2.71/0.91  
% 2.71/0.91  --out_options                           all
% 2.71/0.91  --tptp_safe_out                         true
% 2.71/0.91  --problem_path                          ""
% 2.71/0.91  --include_path                          ""
% 2.71/0.91  --clausifier                            res/vclausify_rel
% 2.71/0.91  --clausifier_options                    --mode clausify
% 2.71/0.91  --stdin                                 false
% 2.71/0.91  --stats_out                             all
% 2.71/0.91  
% 2.71/0.91  ------ General Options
% 2.71/0.91  
% 2.71/0.91  --fof                                   false
% 2.71/0.91  --time_out_real                         305.
% 2.71/0.91  --time_out_virtual                      -1.
% 2.71/0.91  --symbol_type_check                     false
% 2.71/0.91  --clausify_out                          false
% 2.71/0.91  --sig_cnt_out                           false
% 2.71/0.91  --trig_cnt_out                          false
% 2.71/0.91  --trig_cnt_out_tolerance                1.
% 2.71/0.91  --trig_cnt_out_sk_spl                   false
% 2.71/0.91  --abstr_cl_out                          false
% 2.71/0.91  
% 2.71/0.91  ------ Global Options
% 2.71/0.91  
% 2.71/0.91  --schedule                              default
% 2.71/0.91  --add_important_lit                     false
% 2.71/0.91  --prop_solver_per_cl                    1000
% 2.71/0.91  --min_unsat_core                        false
% 2.71/0.91  --soft_assumptions                      false
% 2.71/0.91  --soft_lemma_size                       3
% 2.71/0.91  --prop_impl_unit_size                   0
% 2.71/0.91  --prop_impl_unit                        []
% 2.71/0.91  --share_sel_clauses                     true
% 2.71/0.91  --reset_solvers                         false
% 2.71/0.91  --bc_imp_inh                            [conj_cone]
% 2.71/0.91  --conj_cone_tolerance                   3.
% 2.71/0.91  --extra_neg_conj                        none
% 2.71/0.91  --large_theory_mode                     true
% 2.71/0.91  --prolific_symb_bound                   200
% 2.71/0.91  --lt_threshold                          2000
% 2.71/0.91  --clause_weak_htbl                      true
% 2.71/0.91  --gc_record_bc_elim                     false
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing Options
% 2.71/0.91  
% 2.71/0.91  --preprocessing_flag                    true
% 2.71/0.91  --time_out_prep_mult                    0.1
% 2.71/0.91  --splitting_mode                        input
% 2.71/0.91  --splitting_grd                         true
% 2.71/0.91  --splitting_cvd                         false
% 2.71/0.91  --splitting_cvd_svl                     false
% 2.71/0.91  --splitting_nvd                         32
% 2.71/0.91  --sub_typing                            true
% 2.71/0.91  --prep_gs_sim                           true
% 2.71/0.91  --prep_unflatten                        true
% 2.71/0.91  --prep_res_sim                          true
% 2.71/0.91  --prep_upred                            true
% 2.71/0.91  --prep_sem_filter                       exhaustive
% 2.71/0.91  --prep_sem_filter_out                   false
% 2.71/0.91  --pred_elim                             true
% 2.71/0.91  --res_sim_input                         true
% 2.71/0.91  --eq_ax_congr_red                       true
% 2.71/0.91  --pure_diseq_elim                       true
% 2.71/0.91  --brand_transform                       false
% 2.71/0.91  --non_eq_to_eq                          false
% 2.71/0.91  --prep_def_merge                        true
% 2.71/0.91  --prep_def_merge_prop_impl              false
% 2.71/0.91  --prep_def_merge_mbd                    true
% 2.71/0.91  --prep_def_merge_tr_red                 false
% 2.71/0.91  --prep_def_merge_tr_cl                  false
% 2.71/0.91  --smt_preprocessing                     true
% 2.71/0.91  --smt_ac_axioms                         fast
% 2.71/0.91  --preprocessed_out                      false
% 2.71/0.91  --preprocessed_stats                    false
% 2.71/0.91  
% 2.71/0.91  ------ Abstraction refinement Options
% 2.71/0.91  
% 2.71/0.91  --abstr_ref                             []
% 2.71/0.91  --abstr_ref_prep                        false
% 2.71/0.91  --abstr_ref_until_sat                   false
% 2.71/0.91  --abstr_ref_sig_restrict                funpre
% 2.71/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.91  --abstr_ref_under                       []
% 2.71/0.91  
% 2.71/0.91  ------ SAT Options
% 2.71/0.91  
% 2.71/0.91  --sat_mode                              false
% 2.71/0.91  --sat_fm_restart_options                ""
% 2.71/0.91  --sat_gr_def                            false
% 2.71/0.91  --sat_epr_types                         true
% 2.71/0.91  --sat_non_cyclic_types                  false
% 2.71/0.91  --sat_finite_models                     false
% 2.71/0.91  --sat_fm_lemmas                         false
% 2.71/0.91  --sat_fm_prep                           false
% 2.71/0.91  --sat_fm_uc_incr                        true
% 2.71/0.91  --sat_out_model                         small
% 2.71/0.91  --sat_out_clauses                       false
% 2.71/0.91  
% 2.71/0.91  ------ QBF Options
% 2.71/0.91  
% 2.71/0.91  --qbf_mode                              false
% 2.71/0.91  --qbf_elim_univ                         false
% 2.71/0.91  --qbf_dom_inst                          none
% 2.71/0.91  --qbf_dom_pre_inst                      false
% 2.71/0.91  --qbf_sk_in                             false
% 2.71/0.91  --qbf_pred_elim                         true
% 2.71/0.91  --qbf_split                             512
% 2.71/0.91  
% 2.71/0.91  ------ BMC1 Options
% 2.71/0.91  
% 2.71/0.91  --bmc1_incremental                      false
% 2.71/0.91  --bmc1_axioms                           reachable_all
% 2.71/0.91  --bmc1_min_bound                        0
% 2.71/0.91  --bmc1_max_bound                        -1
% 2.71/0.91  --bmc1_max_bound_default                -1
% 2.71/0.91  --bmc1_symbol_reachability              true
% 2.71/0.91  --bmc1_property_lemmas                  false
% 2.71/0.91  --bmc1_k_induction                      false
% 2.71/0.91  --bmc1_non_equiv_states                 false
% 2.71/0.91  --bmc1_deadlock                         false
% 2.71/0.91  --bmc1_ucm                              false
% 2.71/0.91  --bmc1_add_unsat_core                   none
% 2.71/0.91  --bmc1_unsat_core_children              false
% 2.71/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.91  --bmc1_out_stat                         full
% 2.71/0.91  --bmc1_ground_init                      false
% 2.71/0.91  --bmc1_pre_inst_next_state              false
% 2.71/0.91  --bmc1_pre_inst_state                   false
% 2.71/0.91  --bmc1_pre_inst_reach_state             false
% 2.71/0.91  --bmc1_out_unsat_core                   false
% 2.71/0.91  --bmc1_aig_witness_out                  false
% 2.71/0.91  --bmc1_verbose                          false
% 2.71/0.91  --bmc1_dump_clauses_tptp                false
% 2.71/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.91  --bmc1_dump_file                        -
% 2.71/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.91  --bmc1_ucm_extend_mode                  1
% 2.71/0.91  --bmc1_ucm_init_mode                    2
% 2.71/0.91  --bmc1_ucm_cone_mode                    none
% 2.71/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.91  --bmc1_ucm_relax_model                  4
% 2.71/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.91  --bmc1_ucm_layered_model                none
% 2.71/0.91  --bmc1_ucm_max_lemma_size               10
% 2.71/0.91  
% 2.71/0.91  ------ AIG Options
% 2.71/0.91  
% 2.71/0.91  --aig_mode                              false
% 2.71/0.91  
% 2.71/0.91  ------ Instantiation Options
% 2.71/0.91  
% 2.71/0.91  --instantiation_flag                    true
% 2.71/0.91  --inst_sos_flag                         false
% 2.71/0.91  --inst_sos_phase                        true
% 2.71/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.91  --inst_lit_sel_side                     none
% 2.71/0.91  --inst_solver_per_active                1400
% 2.71/0.91  --inst_solver_calls_frac                1.
% 2.71/0.91  --inst_passive_queue_type               priority_queues
% 2.71/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.91  --inst_passive_queues_freq              [25;2]
% 2.71/0.91  --inst_dismatching                      true
% 2.71/0.91  --inst_eager_unprocessed_to_passive     true
% 2.71/0.91  --inst_prop_sim_given                   true
% 2.71/0.91  --inst_prop_sim_new                     false
% 2.71/0.91  --inst_subs_new                         false
% 2.71/0.91  --inst_eq_res_simp                      false
% 2.71/0.91  --inst_subs_given                       false
% 2.71/0.91  --inst_orphan_elimination               true
% 2.71/0.91  --inst_learning_loop_flag               true
% 2.71/0.91  --inst_learning_start                   3000
% 2.71/0.91  --inst_learning_factor                  2
% 2.71/0.91  --inst_start_prop_sim_after_learn       3
% 2.71/0.91  --inst_sel_renew                        solver
% 2.71/0.91  --inst_lit_activity_flag                true
% 2.71/0.91  --inst_restr_to_given                   false
% 2.71/0.91  --inst_activity_threshold               500
% 2.71/0.91  --inst_out_proof                        true
% 2.71/0.91  
% 2.71/0.91  ------ Resolution Options
% 2.71/0.91  
% 2.71/0.91  --resolution_flag                       false
% 2.71/0.91  --res_lit_sel                           adaptive
% 2.71/0.91  --res_lit_sel_side                      none
% 2.71/0.91  --res_ordering                          kbo
% 2.71/0.91  --res_to_prop_solver                    active
% 2.71/0.91  --res_prop_simpl_new                    false
% 2.71/0.91  --res_prop_simpl_given                  true
% 2.71/0.91  --res_passive_queue_type                priority_queues
% 2.71/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.91  --res_passive_queues_freq               [15;5]
% 2.71/0.91  --res_forward_subs                      full
% 2.71/0.91  --res_backward_subs                     full
% 2.71/0.91  --res_forward_subs_resolution           true
% 2.71/0.91  --res_backward_subs_resolution          true
% 2.71/0.91  --res_orphan_elimination                true
% 2.71/0.91  --res_time_limit                        2.
% 2.71/0.91  --res_out_proof                         true
% 2.71/0.91  
% 2.71/0.91  ------ Superposition Options
% 2.71/0.91  
% 2.71/0.91  --superposition_flag                    true
% 2.71/0.91  --sup_passive_queue_type                priority_queues
% 2.71/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.91  --demod_completeness_check              fast
% 2.71/0.91  --demod_use_ground                      true
% 2.71/0.91  --sup_to_prop_solver                    passive
% 2.71/0.91  --sup_prop_simpl_new                    true
% 2.71/0.91  --sup_prop_simpl_given                  true
% 2.71/0.91  --sup_fun_splitting                     false
% 2.71/0.91  --sup_smt_interval                      50000
% 2.71/0.91  
% 2.71/0.91  ------ Superposition Simplification Setup
% 2.71/0.91  
% 2.71/0.91  --sup_indices_passive                   []
% 2.71/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_full_bw                           [BwDemod]
% 2.71/0.91  --sup_immed_triv                        [TrivRules]
% 2.71/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_immed_bw_main                     []
% 2.71/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.91  
% 2.71/0.91  ------ Combination Options
% 2.71/0.91  
% 2.71/0.91  --comb_res_mult                         3
% 2.71/0.91  --comb_sup_mult                         2
% 2.71/0.91  --comb_inst_mult                        10
% 2.71/0.91  
% 2.71/0.91  ------ Debug Options
% 2.71/0.91  
% 2.71/0.91  --dbg_backtrace                         false
% 2.71/0.91  --dbg_dump_prop_clauses                 false
% 2.71/0.91  --dbg_dump_prop_clauses_file            -
% 2.71/0.91  --dbg_out_stat                          false
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  ------ Proving...
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  % SZS status Theorem for theBenchmark.p
% 2.71/0.91  
% 2.71/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/0.91  
% 2.71/0.91  fof(f17,conjecture,(
% 2.71/0.91    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f18,negated_conjecture,(
% 2.71/0.91    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.71/0.91    inference(negated_conjecture,[],[f17])).
% 2.71/0.91  
% 2.71/0.91  fof(f20,plain,(
% 2.71/0.91    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.71/0.91    inference(pure_predicate_removal,[],[f18])).
% 2.71/0.91  
% 2.71/0.91  fof(f31,plain,(
% 2.71/0.91    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 2.71/0.91    inference(ennf_transformation,[],[f20])).
% 2.71/0.91  
% 2.71/0.91  fof(f32,plain,(
% 2.71/0.91    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 2.71/0.91    inference(flattening,[],[f31])).
% 2.71/0.91  
% 2.71/0.91  fof(f43,plain,(
% 2.71/0.91    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3))),
% 2.71/0.91    introduced(choice_axiom,[])).
% 2.71/0.91  
% 2.71/0.91  fof(f44,plain,(
% 2.71/0.91    (~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3)),
% 2.71/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f43])).
% 2.71/0.91  
% 2.71/0.91  fof(f77,plain,(
% 2.71/0.91    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 2.71/0.91    inference(cnf_transformation,[],[f44])).
% 2.71/0.91  
% 2.71/0.91  fof(f16,axiom,(
% 2.71/0.91    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f75,plain,(
% 2.71/0.91    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f16])).
% 2.71/0.91  
% 2.71/0.91  fof(f82,plain,(
% 2.71/0.91    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 2.71/0.91    inference(definition_unfolding,[],[f77,f75])).
% 2.71/0.91  
% 2.71/0.91  fof(f15,axiom,(
% 2.71/0.91    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f19,plain,(
% 2.71/0.91    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 2.71/0.91    inference(pure_predicate_removal,[],[f15])).
% 2.71/0.91  
% 2.71/0.91  fof(f30,plain,(
% 2.71/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.71/0.91    inference(ennf_transformation,[],[f19])).
% 2.71/0.91  
% 2.71/0.91  fof(f74,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f30])).
% 2.71/0.91  
% 2.71/0.91  fof(f80,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.71/0.91    inference(definition_unfolding,[],[f74,f75])).
% 2.71/0.91  
% 2.71/0.91  fof(f7,axiom,(
% 2.71/0.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f41,plain,(
% 2.71/0.91    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.71/0.91    inference(nnf_transformation,[],[f7])).
% 2.71/0.91  
% 2.71/0.91  fof(f56,plain,(
% 2.71/0.91    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f41])).
% 2.71/0.91  
% 2.71/0.91  fof(f9,axiom,(
% 2.71/0.91    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f22,plain,(
% 2.71/0.91    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.71/0.91    inference(ennf_transformation,[],[f9])).
% 2.71/0.91  
% 2.71/0.91  fof(f60,plain,(
% 2.71/0.91    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.71/0.91    inference(cnf_transformation,[],[f22])).
% 2.71/0.91  
% 2.71/0.91  fof(f10,axiom,(
% 2.71/0.91    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f23,plain,(
% 2.71/0.91    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.71/0.91    inference(ennf_transformation,[],[f10])).
% 2.71/0.91  
% 2.71/0.91  fof(f24,plain,(
% 2.71/0.91    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.71/0.91    inference(flattening,[],[f23])).
% 2.71/0.91  
% 2.71/0.91  fof(f62,plain,(
% 2.71/0.91    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f24])).
% 2.71/0.91  
% 2.71/0.91  fof(f8,axiom,(
% 2.71/0.91    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f58,plain,(
% 2.71/0.91    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f8])).
% 2.71/0.91  
% 2.71/0.91  fof(f76,plain,(
% 2.71/0.91    v1_relat_1(sK3)),
% 2.71/0.91    inference(cnf_transformation,[],[f44])).
% 2.71/0.91  
% 2.71/0.91  fof(f73,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f30])).
% 2.71/0.91  
% 2.71/0.91  fof(f81,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.71/0.91    inference(definition_unfolding,[],[f73,f75])).
% 2.71/0.91  
% 2.71/0.91  fof(f13,axiom,(
% 2.71/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f26,plain,(
% 2.71/0.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.91    inference(ennf_transformation,[],[f13])).
% 2.71/0.91  
% 2.71/0.91  fof(f27,plain,(
% 2.71/0.91    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.91    inference(flattening,[],[f26])).
% 2.71/0.91  
% 2.71/0.91  fof(f42,plain,(
% 2.71/0.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.91    inference(nnf_transformation,[],[f27])).
% 2.71/0.91  
% 2.71/0.91  fof(f66,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f42])).
% 2.71/0.91  
% 2.71/0.91  fof(f12,axiom,(
% 2.71/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f25,plain,(
% 2.71/0.91    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.91    inference(ennf_transformation,[],[f12])).
% 2.71/0.91  
% 2.71/0.91  fof(f65,plain,(
% 2.71/0.91    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.91    inference(cnf_transformation,[],[f25])).
% 2.71/0.91  
% 2.71/0.91  fof(f78,plain,(
% 2.71/0.91    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1),
% 2.71/0.91    inference(cnf_transformation,[],[f44])).
% 2.71/0.91  
% 2.71/0.91  fof(f4,axiom,(
% 2.71/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f37,plain,(
% 2.71/0.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.91    inference(nnf_transformation,[],[f4])).
% 2.71/0.91  
% 2.71/0.91  fof(f38,plain,(
% 2.71/0.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.91    inference(flattening,[],[f37])).
% 2.71/0.91  
% 2.71/0.91  fof(f51,plain,(
% 2.71/0.91    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f38])).
% 2.71/0.91  
% 2.71/0.91  fof(f6,axiom,(
% 2.71/0.91    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f39,plain,(
% 2.71/0.91    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.71/0.91    inference(nnf_transformation,[],[f6])).
% 2.71/0.91  
% 2.71/0.91  fof(f40,plain,(
% 2.71/0.91    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.71/0.91    inference(flattening,[],[f39])).
% 2.71/0.91  
% 2.71/0.91  fof(f54,plain,(
% 2.71/0.91    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.71/0.91    inference(cnf_transformation,[],[f40])).
% 2.71/0.91  
% 2.71/0.91  fof(f86,plain,(
% 2.71/0.91    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.71/0.91    inference(equality_resolution,[],[f54])).
% 2.71/0.91  
% 2.71/0.91  fof(f5,axiom,(
% 2.71/0.91    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f52,plain,(
% 2.71/0.91    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f5])).
% 2.71/0.91  
% 2.71/0.91  fof(f55,plain,(
% 2.71/0.91    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.71/0.91    inference(cnf_transformation,[],[f40])).
% 2.71/0.91  
% 2.71/0.91  fof(f85,plain,(
% 2.71/0.91    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.71/0.91    inference(equality_resolution,[],[f55])).
% 2.71/0.91  
% 2.71/0.91  fof(f53,plain,(
% 2.71/0.91    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f40])).
% 2.71/0.91  
% 2.71/0.91  fof(f11,axiom,(
% 2.71/0.91    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f64,plain,(
% 2.71/0.91    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.71/0.91    inference(cnf_transformation,[],[f11])).
% 2.71/0.91  
% 2.71/0.91  fof(f63,plain,(
% 2.71/0.91    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.71/0.91    inference(cnf_transformation,[],[f11])).
% 2.71/0.91  
% 2.71/0.91  fof(f14,axiom,(
% 2.71/0.91    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f28,plain,(
% 2.71/0.91    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.71/0.91    inference(ennf_transformation,[],[f14])).
% 2.71/0.91  
% 2.71/0.91  fof(f29,plain,(
% 2.71/0.91    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.71/0.91    inference(flattening,[],[f28])).
% 2.71/0.91  
% 2.71/0.91  fof(f72,plain,(
% 2.71/0.91    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f29])).
% 2.71/0.91  
% 2.71/0.91  fof(f79,plain,(
% 2.71/0.91    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.71/0.91    inference(definition_unfolding,[],[f72,f75])).
% 2.71/0.91  
% 2.71/0.91  fof(f1,axiom,(
% 2.71/0.91    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f33,plain,(
% 2.71/0.91    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.71/0.91    inference(nnf_transformation,[],[f1])).
% 2.71/0.91  
% 2.71/0.91  fof(f34,plain,(
% 2.71/0.91    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.71/0.91    inference(rectify,[],[f33])).
% 2.71/0.91  
% 2.71/0.91  fof(f35,plain,(
% 2.71/0.91    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.71/0.91    introduced(choice_axiom,[])).
% 2.71/0.91  
% 2.71/0.91  fof(f36,plain,(
% 2.71/0.91    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.71/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.71/0.91  
% 2.71/0.91  fof(f45,plain,(
% 2.71/0.91    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f36])).
% 2.71/0.91  
% 2.71/0.91  fof(f3,axiom,(
% 2.71/0.91    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f21,plain,(
% 2.71/0.91    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.71/0.91    inference(ennf_transformation,[],[f3])).
% 2.71/0.91  
% 2.71/0.91  fof(f48,plain,(
% 2.71/0.91    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.71/0.91    inference(cnf_transformation,[],[f21])).
% 2.71/0.91  
% 2.71/0.91  fof(f2,axiom,(
% 2.71/0.91    v1_xboole_0(k1_xboole_0)),
% 2.71/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.91  
% 2.71/0.91  fof(f47,plain,(
% 2.71/0.91    v1_xboole_0(k1_xboole_0)),
% 2.71/0.91    inference(cnf_transformation,[],[f2])).
% 2.71/0.91  
% 2.71/0.91  cnf(c_31,negated_conjecture,
% 2.71/0.91      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
% 2.71/0.91      inference(cnf_transformation,[],[f82]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1884,plain,
% 2.71/0.91      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_28,plain,
% 2.71/0.91      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.91      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.71/0.91      inference(cnf_transformation,[],[f80]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1886,plain,
% 2.71/0.91      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.71/0.91      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3384,plain,
% 2.71/0.91      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_1884,c_1886]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_12,plain,
% 2.71/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.71/0.91      inference(cnf_transformation,[],[f56]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1892,plain,
% 2.71/0.91      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.71/0.91      | r1_tarski(X0,X1) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3535,plain,
% 2.71/0.91      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3384,c_1892]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_14,plain,
% 2.71/0.91      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 2.71/0.91      | k1_xboole_0 = X0
% 2.71/0.91      | k1_xboole_0 = X1 ),
% 2.71/0.91      inference(cnf_transformation,[],[f60]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_16,plain,
% 2.71/0.91      ( ~ r1_tarski(X0,X1)
% 2.71/0.91      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.71/0.91      | ~ v1_relat_1(X1)
% 2.71/0.91      | ~ v1_relat_1(X0) ),
% 2.71/0.91      inference(cnf_transformation,[],[f62]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1890,plain,
% 2.71/0.91      ( r1_tarski(X0,X1) != iProver_top
% 2.71/0.91      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.71/0.91      | v1_relat_1(X1) != iProver_top
% 2.71/0.91      | v1_relat_1(X0) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_4303,plain,
% 2.71/0.91      ( k1_xboole_0 = X0
% 2.71/0.91      | k1_xboole_0 = X1
% 2.71/0.91      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.71/0.91      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.71/0.91      | v1_relat_1(X2) != iProver_top
% 2.71/0.91      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_14,c_1890]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_13,plain,
% 2.71/0.91      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.71/0.91      inference(cnf_transformation,[],[f58]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_72,plain,
% 2.71/0.91      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5916,plain,
% 2.71/0.91      ( v1_relat_1(X2) != iProver_top
% 2.71/0.91      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.71/0.91      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.71/0.91      | k1_xboole_0 = X1
% 2.71/0.91      | k1_xboole_0 = X0 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_4303,c_72]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5917,plain,
% 2.71/0.91      ( k1_xboole_0 = X0
% 2.71/0.91      | k1_xboole_0 = X1
% 2.71/0.91      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.71/0.91      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.71/0.91      | v1_relat_1(X2) != iProver_top ),
% 2.71/0.91      inference(renaming,[status(thm)],[c_5916]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5927,plain,
% 2.71/0.91      ( sK1 = k1_xboole_0
% 2.71/0.91      | sK2 = k1_xboole_0
% 2.71/0.91      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.71/0.91      | v1_relat_1(sK3) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3535,c_5917]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_32,negated_conjecture,
% 2.71/0.91      ( v1_relat_1(sK3) ),
% 2.71/0.91      inference(cnf_transformation,[],[f76]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_29,plain,
% 2.71/0.91      ( v1_funct_2(X0,X1,X2)
% 2.71/0.91      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.71/0.91      inference(cnf_transformation,[],[f81]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_26,plain,
% 2.71/0.91      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.91      | k1_xboole_0 = X2 ),
% 2.71/0.91      inference(cnf_transformation,[],[f66]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_724,plain,
% 2.71/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.91      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.91      | k1_xboole_0 = X2 ),
% 2.71/0.91      inference(resolution,[status(thm)],[c_29,c_26]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_427,plain,
% 2.71/0.91      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/0.91      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.91      | k1_xboole_0 = X2 ),
% 2.71/0.91      inference(resolution,[status(thm)],[c_28,c_26]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_431,plain,
% 2.71/0.91      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.91      | k1_xboole_0 = X2 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_427,c_29]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_728,plain,
% 2.71/0.91      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.91      | k1_xboole_0 = X2 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_724,c_29,c_427]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1882,plain,
% 2.71/0.91      ( k1_relset_1(X0,X1,X2) = X0
% 2.71/0.91      | k1_xboole_0 = X1
% 2.71/0.91      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3166,plain,
% 2.71/0.91      ( k1_relset_1(sK1,sK2,sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_1884,c_1882]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_20,plain,
% 2.71/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.91      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.71/0.91      inference(cnf_transformation,[],[f65]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1888,plain,
% 2.71/0.91      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.71/0.91      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3536,plain,
% 2.71/0.91      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3384,c_1888]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3616,plain,
% 2.71/0.91      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3166,c_3536]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_30,negated_conjecture,
% 2.71/0.91      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1 ),
% 2.71/0.91      inference(cnf_transformation,[],[f78]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1885,plain,
% 2.71/0.91      ( k1_relat_1(sK3) != sK1
% 2.71/0.91      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3803,plain,
% 2.71/0.91      ( sK2 = k1_xboole_0
% 2.71/0.91      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3616,c_1885]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3804,plain,
% 2.71/0.91      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(predicate_to_equality_rev,[status(thm)],[c_3803]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5952,plain,
% 2.71/0.91      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.71/0.91      | ~ v1_relat_1(sK3)
% 2.71/0.91      | sK1 = k1_xboole_0
% 2.71/0.91      | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(predicate_to_equality_rev,[status(thm)],[c_5927]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5954,plain,
% 2.71/0.91      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_5927,c_32,c_3804,c_5952]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_4,plain,
% 2.71/0.91      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.71/0.91      inference(cnf_transformation,[],[f51]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1896,plain,
% 2.71/0.91      ( X0 = X1
% 2.71/0.91      | r1_tarski(X0,X1) != iProver_top
% 2.71/0.91      | r1_tarski(X1,X0) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3608,plain,
% 2.71/0.91      ( k2_zfmisc_1(sK1,sK2) = sK3
% 2.71/0.91      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_3535,c_1896]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_5963,plain,
% 2.71/0.91      ( k2_zfmisc_1(sK1,sK2) = sK3
% 2.71/0.91      | sK2 = k1_xboole_0
% 2.71/0.91      | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_5954,c_3608]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_9,plain,
% 2.71/0.91      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.71/0.91      inference(cnf_transformation,[],[f86]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6001,plain,
% 2.71/0.91      ( k2_zfmisc_1(sK1,sK2) = sK3
% 2.71/0.91      | sK2 = k1_xboole_0
% 2.71/0.91      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.71/0.91      inference(demodulation,[status(thm)],[c_5963,c_9]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,X0) ),
% 2.71/0.91      inference(cnf_transformation,[],[f52]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2374,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,sK3) ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_7]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2377,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6787,plain,
% 2.71/0.91      ( sK2 = k1_xboole_0 | k2_zfmisc_1(sK1,sK2) = sK3 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_6001,c_2377]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6788,plain,
% 2.71/0.91      ( k2_zfmisc_1(sK1,sK2) = sK3 | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(renaming,[status(thm)],[c_6787]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6791,plain,
% 2.71/0.91      ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3 | sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_5954,c_6788]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6837,plain,
% 2.71/0.91      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.71/0.91      inference(demodulation,[status(thm)],[c_6791,c_9]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7070,plain,
% 2.71/0.91      ( sK3 = k1_xboole_0
% 2.71/0.91      | r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0))) = iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_6837,c_1884]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2520,plain,
% 2.71/0.91      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_4]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2521,plain,
% 2.71/0.91      ( sK3 = X0
% 2.71/0.91      | r1_tarski(X0,sK3) != iProver_top
% 2.71/0.91      | r1_tarski(sK3,X0) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2523,plain,
% 2.71/0.91      ( sK3 = k1_xboole_0
% 2.71/0.91      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 2.71/0.91      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_2521]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7065,plain,
% 2.71/0.91      ( sK3 = k1_xboole_0
% 2.71/0.91      | r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_6837,c_3535]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_8,plain,
% 2.71/0.91      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.71/0.91      inference(cnf_transformation,[],[f85]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7087,plain,
% 2.71/0.91      ( sK3 = k1_xboole_0 | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.71/0.91      inference(demodulation,[status(thm)],[c_7065,c_8]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_10,plain,
% 2.71/0.91      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.71/0.91      | k1_xboole_0 = X0
% 2.71/0.91      | k1_xboole_0 = X1 ),
% 2.71/0.91      inference(cnf_transformation,[],[f53]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_81,plain,
% 2.71/0.91      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.71/0.91      | k1_xboole_0 = k1_xboole_0 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_10]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_82,plain,
% 2.71/0.91      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_9]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_83,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_85,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_83]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1338,plain,
% 2.71/0.91      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.71/0.91      theory(equality) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2928,plain,
% 2.71/0.91      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_1338]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2929,plain,
% 2.71/0.91      ( X0 != X1
% 2.71/0.91      | sK3 != X2
% 2.71/0.91      | r1_tarski(X2,X1) != iProver_top
% 2.71/0.91      | r1_tarski(sK3,X0) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_2928]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2931,plain,
% 2.71/0.91      ( sK3 != k1_xboole_0
% 2.71/0.91      | k1_xboole_0 != k1_xboole_0
% 2.71/0.91      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 2.71/0.91      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7114,plain,
% 2.71/0.91      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_7087,c_81,c_82,c_85,c_2931]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7231,plain,
% 2.71/0.91      ( sK3 = k1_xboole_0 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_7070,c_81,c_82,c_85,c_2377,c_2523,c_2931,c_7087]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7259,plain,
% 2.71/0.91      ( k1_relat_1(k1_xboole_0) != sK1
% 2.71/0.91      | r1_tarski(k2_relat_1(k1_xboole_0),sK2) != iProver_top ),
% 2.71/0.91      inference(demodulation,[status(thm)],[c_7231,c_1885]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_18,plain,
% 2.71/0.91      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.71/0.91      inference(cnf_transformation,[],[f64]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_19,plain,
% 2.71/0.91      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.71/0.91      inference(cnf_transformation,[],[f63]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7266,plain,
% 2.71/0.91      ( sK1 != k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.71/0.91      inference(light_normalisation,[status(thm)],[c_7259,c_18,c_19]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2483,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_7]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2486,plain,
% 2.71/0.91      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7498,plain,
% 2.71/0.91      ( sK1 != k1_xboole_0 ),
% 2.71/0.91      inference(global_propositional_subsumption,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_7266,c_2486]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7501,plain,
% 2.71/0.91      ( sK2 = k1_xboole_0 ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_5954,c_7498]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_27,plain,
% 2.71/0.91      ( ~ v1_xboole_0(X0)
% 2.71/0.91      | v1_xboole_0(X1)
% 2.71/0.91      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 2.71/0.91      inference(cnf_transformation,[],[f79]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1887,plain,
% 2.71/0.91      ( v1_xboole_0(X0) != iProver_top
% 2.71/0.91      | v1_xboole_0(X1) = iProver_top
% 2.71/0.91      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1,plain,
% 2.71/0.91      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.71/0.91      inference(cnf_transformation,[],[f45]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1899,plain,
% 2.71/0.91      ( r2_hidden(X0,X1) != iProver_top
% 2.71/0.91      | v1_xboole_0(X1) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2581,plain,
% 2.71/0.91      ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_1884,c_1899]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3398,plain,
% 2.71/0.91      ( v1_xboole_0(sK1) = iProver_top
% 2.71/0.91      | v1_xboole_0(sK2) != iProver_top ),
% 2.71/0.91      inference(superposition,[status(thm)],[c_1887,c_2581]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_7684,plain,
% 2.71/0.91      ( v1_xboole_0(sK1) = iProver_top
% 2.71/0.91      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.71/0.91      inference(demodulation,[status(thm)],[c_7501,c_3398]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1335,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3438,plain,
% 2.71/0.91      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_1335]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6874,plain,
% 2.71/0.91      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_3438]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_6875,plain,
% 2.71/0.91      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_6874]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3,plain,
% 2.71/0.91      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.71/0.91      inference(cnf_transformation,[],[f48]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3483,plain,
% 2.71/0.91      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_3]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3484,plain,
% 2.71/0.91      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_3483]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_1334,plain,( X0 = X0 ),theory(equality) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_3445,plain,
% 2.71/0.91      ( sK1 = sK1 ),
% 2.71/0.91      inference(instantiation,[status(thm)],[c_1334]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_2,plain,
% 2.71/0.91      ( v1_xboole_0(k1_xboole_0) ),
% 2.71/0.91      inference(cnf_transformation,[],[f47]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(c_94,plain,
% 2.71/0.91      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.71/0.91      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.71/0.91  
% 2.71/0.91  cnf(contradiction,plain,
% 2.71/0.91      ( $false ),
% 2.71/0.91      inference(minisat,
% 2.71/0.91                [status(thm)],
% 2.71/0.91                [c_7684,c_7266,c_6875,c_3484,c_3445,c_2486,c_94]) ).
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/0.91  
% 2.71/0.91  ------                               Statistics
% 2.71/0.91  
% 2.71/0.91  ------ General
% 2.71/0.91  
% 2.71/0.91  abstr_ref_over_cycles:                  0
% 2.71/0.91  abstr_ref_under_cycles:                 0
% 2.71/0.91  gc_basic_clause_elim:                   0
% 2.71/0.91  forced_gc_time:                         0
% 2.71/0.91  parsing_time:                           0.008
% 2.71/0.91  unif_index_cands_time:                  0.
% 2.71/0.91  unif_index_add_time:                    0.
% 2.71/0.91  orderings_time:                         0.
% 2.71/0.91  out_proof_time:                         0.01
% 2.71/0.91  total_time:                             0.207
% 2.71/0.91  num_of_symbols:                         49
% 2.71/0.91  num_of_terms:                           4723
% 2.71/0.91  
% 2.71/0.91  ------ Preprocessing
% 2.71/0.91  
% 2.71/0.91  num_of_splits:                          0
% 2.71/0.91  num_of_split_atoms:                     0
% 2.71/0.91  num_of_reused_defs:                     0
% 2.71/0.91  num_eq_ax_congr_red:                    11
% 2.71/0.91  num_of_sem_filtered_clauses:            1
% 2.71/0.91  num_of_subtypes:                        0
% 2.71/0.91  monotx_restored_types:                  0
% 2.71/0.91  sat_num_of_epr_types:                   0
% 2.71/0.91  sat_num_of_non_cyclic_types:            0
% 2.71/0.91  sat_guarded_non_collapsed_types:        0
% 2.71/0.91  num_pure_diseq_elim:                    0
% 2.71/0.91  simp_replaced_by:                       0
% 2.71/0.91  res_preprocessed:                       145
% 2.71/0.91  prep_upred:                             0
% 2.71/0.91  prep_unflattend:                        84
% 2.71/0.91  smt_new_axioms:                         0
% 2.71/0.91  pred_elim_cands:                        5
% 2.71/0.91  pred_elim:                              1
% 2.71/0.91  pred_elim_cl:                           4
% 2.71/0.91  pred_elim_cycles:                       7
% 2.71/0.91  merged_defs:                            8
% 2.71/0.91  merged_defs_ncl:                        0
% 2.71/0.91  bin_hyper_res:                          8
% 2.71/0.91  prep_cycles:                            4
% 2.71/0.91  pred_elim_time:                         0.015
% 2.71/0.91  splitting_time:                         0.
% 2.71/0.91  sem_filter_time:                        0.
% 2.71/0.91  monotx_time:                            0.
% 2.71/0.91  subtype_inf_time:                       0.
% 2.71/0.91  
% 2.71/0.91  ------ Problem properties
% 2.71/0.91  
% 2.71/0.91  clauses:                                28
% 2.71/0.91  conjectures:                            3
% 2.71/0.91  epr:                                    7
% 2.71/0.91  horn:                                   21
% 2.71/0.91  ground:                                 6
% 2.71/0.91  unary:                                  10
% 2.71/0.91  binary:                                 9
% 2.71/0.91  lits:                                   57
% 2.71/0.91  lits_eq:                                22
% 2.71/0.91  fd_pure:                                0
% 2.71/0.91  fd_pseudo:                              0
% 2.71/0.91  fd_cond:                                3
% 2.71/0.91  fd_pseudo_cond:                         1
% 2.71/0.91  ac_symbols:                             0
% 2.71/0.91  
% 2.71/0.91  ------ Propositional Solver
% 2.71/0.91  
% 2.71/0.91  prop_solver_calls:                      29
% 2.71/0.91  prop_fast_solver_calls:                 1195
% 2.71/0.91  smt_solver_calls:                       0
% 2.71/0.91  smt_fast_solver_calls:                  0
% 2.71/0.91  prop_num_of_clauses:                    2226
% 2.71/0.91  prop_preprocess_simplified:             6399
% 2.71/0.91  prop_fo_subsumed:                       47
% 2.71/0.91  prop_solver_time:                       0.
% 2.71/0.91  smt_solver_time:                        0.
% 2.71/0.91  smt_fast_solver_time:                   0.
% 2.71/0.91  prop_fast_solver_time:                  0.
% 2.71/0.91  prop_unsat_core_time:                   0.
% 2.71/0.91  
% 2.71/0.91  ------ QBF
% 2.71/0.91  
% 2.71/0.91  qbf_q_res:                              0
% 2.71/0.91  qbf_num_tautologies:                    0
% 2.71/0.91  qbf_prep_cycles:                        0
% 2.71/0.91  
% 2.71/0.91  ------ BMC1
% 2.71/0.91  
% 2.71/0.91  bmc1_current_bound:                     -1
% 2.71/0.91  bmc1_last_solved_bound:                 -1
% 2.71/0.91  bmc1_unsat_core_size:                   -1
% 2.71/0.91  bmc1_unsat_core_parents_size:           -1
% 2.71/0.91  bmc1_merge_next_fun:                    0
% 2.71/0.91  bmc1_unsat_core_clauses_time:           0.
% 2.71/0.91  
% 2.71/0.91  ------ Instantiation
% 2.71/0.91  
% 2.71/0.91  inst_num_of_clauses:                    723
% 2.71/0.91  inst_num_in_passive:                    360
% 2.71/0.91  inst_num_in_active:                     363
% 2.71/0.91  inst_num_in_unprocessed:                0
% 2.71/0.91  inst_num_of_loops:                      470
% 2.71/0.91  inst_num_of_learning_restarts:          0
% 2.71/0.91  inst_num_moves_active_passive:          102
% 2.71/0.91  inst_lit_activity:                      0
% 2.71/0.91  inst_lit_activity_moves:                0
% 2.71/0.91  inst_num_tautologies:                   0
% 2.71/0.91  inst_num_prop_implied:                  0
% 2.71/0.91  inst_num_existing_simplified:           0
% 2.71/0.91  inst_num_eq_res_simplified:             0
% 2.71/0.91  inst_num_child_elim:                    0
% 2.71/0.91  inst_num_of_dismatching_blockings:      142
% 2.71/0.91  inst_num_of_non_proper_insts:           644
% 2.71/0.91  inst_num_of_duplicates:                 0
% 2.71/0.91  inst_inst_num_from_inst_to_res:         0
% 2.71/0.91  inst_dismatching_checking_time:         0.
% 2.71/0.91  
% 2.71/0.91  ------ Resolution
% 2.71/0.91  
% 2.71/0.91  res_num_of_clauses:                     0
% 2.71/0.91  res_num_in_passive:                     0
% 2.71/0.91  res_num_in_active:                      0
% 2.71/0.91  res_num_of_loops:                       149
% 2.71/0.91  res_forward_subset_subsumed:            66
% 2.71/0.91  res_backward_subset_subsumed:           2
% 2.71/0.91  res_forward_subsumed:                   0
% 2.71/0.91  res_backward_subsumed:                  0
% 2.71/0.91  res_forward_subsumption_resolution:     3
% 2.71/0.91  res_backward_subsumption_resolution:    0
% 2.71/0.91  res_clause_to_clause_subsumption:       634
% 2.71/0.91  res_orphan_elimination:                 0
% 2.71/0.91  res_tautology_del:                      69
% 2.71/0.91  res_num_eq_res_simplified:              0
% 2.71/0.91  res_num_sel_changes:                    0
% 2.71/0.91  res_moves_from_active_to_pass:          0
% 2.71/0.91  
% 2.71/0.91  ------ Superposition
% 2.71/0.91  
% 2.71/0.91  sup_time_total:                         0.
% 2.71/0.91  sup_time_generating:                    0.
% 2.71/0.91  sup_time_sim_full:                      0.
% 2.71/0.91  sup_time_sim_immed:                     0.
% 2.71/0.91  
% 2.71/0.91  sup_num_of_clauses:                     82
% 2.71/0.91  sup_num_in_active:                      49
% 2.71/0.91  sup_num_in_passive:                     33
% 2.71/0.91  sup_num_of_loops:                       93
% 2.71/0.91  sup_fw_superposition:                   117
% 2.71/0.91  sup_bw_superposition:                   122
% 2.71/0.91  sup_immediate_simplified:               88
% 2.71/0.91  sup_given_eliminated:                   0
% 2.71/0.91  comparisons_done:                       0
% 2.71/0.91  comparisons_avoided:                    34
% 2.71/0.91  
% 2.71/0.91  ------ Simplifications
% 2.71/0.91  
% 2.71/0.91  
% 2.71/0.91  sim_fw_subset_subsumed:                 40
% 2.71/0.91  sim_bw_subset_subsumed:                 29
% 2.71/0.91  sim_fw_subsumed:                        23
% 2.71/0.91  sim_bw_subsumed:                        0
% 2.71/0.91  sim_fw_subsumption_res:                 7
% 2.71/0.91  sim_bw_subsumption_res:                 0
% 2.71/0.91  sim_tautology_del:                      4
% 2.71/0.91  sim_eq_tautology_del:                   29
% 2.71/0.91  sim_eq_res_simp:                        0
% 2.71/0.91  sim_fw_demodulated:                     14
% 2.71/0.91  sim_bw_demodulated:                     34
% 2.71/0.91  sim_light_normalised:                   17
% 2.71/0.91  sim_joinable_taut:                      0
% 2.71/0.91  sim_joinable_simp:                      0
% 2.71/0.91  sim_ac_normalised:                      0
% 2.71/0.91  sim_smt_subsumption:                    0
% 2.71/0.91  
%------------------------------------------------------------------------------
