%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:56 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  153 (1479 expanded)
%              Number of clauses        :   80 ( 482 expanded)
%              Number of leaves         :   22 ( 289 expanded)
%              Depth                    :   29
%              Number of atoms          :  387 (4316 expanded)
%              Number of equality atoms :  210 (1787 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f43])).

fof(f76,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1860,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1862,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3186,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_1862])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3453,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_1868])).

cnf(c_13,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1866,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3827,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1866])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1867,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5389,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X0) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3827,c_1867])).

cnf(c_5392,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3453,c_5389])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_28,c_25])).

cnf(c_415,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_27,c_25])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_28])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_28,c_415])).

cnf(c_1858,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_3050,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1860,c_1858])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1864,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3454,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3186,c_1864])).

cnf(c_3518,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3050,c_3454])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1861,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3593,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_1861])).

cnf(c_3633,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3593])).

cnf(c_5408,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5392])).

cnf(c_5509,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5392,c_31,c_3633,c_5408])).

cnf(c_5530,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5509,c_3453])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5556,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5530,c_8])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1871,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6028,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5556,c_1871])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1870,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2543,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1870,c_1871])).

cnf(c_2585,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_2543])).

cnf(c_6044,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6028,c_2585])).

cnf(c_3516,plain,
    ( k2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2)) = k2_zfmisc_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3453,c_1871])).

cnf(c_7198,plain,
    ( k2_xboole_0(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = k2_zfmisc_1(sK1,sK2)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6044,c_3516])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7239,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7198,c_7,c_2585])).

cnf(c_7283,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6044,c_7239])).

cnf(c_7330,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7283,c_7])).

cnf(c_7448,plain,
    ( k1_relat_1(k1_xboole_0) != sK1
    | r1_tarski(k2_relat_1(k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7330,c_1861])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7455,plain,
    ( sK1 != k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7448,c_17,c_18])).

cnf(c_2452,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2455,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2452])).

cnf(c_7630,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7455,c_2455])).

cnf(c_7633,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5509,c_7630])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1863,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1874,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2736,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_1874])).

cnf(c_3200,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1863,c_2736])).

cnf(c_7682,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7633,c_3200])).

cnf(c_1325,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3388,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_6812,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_6813,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_6812])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3414,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3415,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3414])).

cnf(c_1324,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3386,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_91,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7682,c_7455,c_6813,c_3415,c_3386,c_2455,c_91])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.89/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/1.01  
% 2.89/1.01  ------  iProver source info
% 2.89/1.01  
% 2.89/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.89/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/1.01  git: non_committed_changes: false
% 2.89/1.01  git: last_make_outside_of_git: false
% 2.89/1.01  
% 2.89/1.01  ------ 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options
% 2.89/1.01  
% 2.89/1.01  --out_options                           all
% 2.89/1.01  --tptp_safe_out                         true
% 2.89/1.01  --problem_path                          ""
% 2.89/1.01  --include_path                          ""
% 2.89/1.01  --clausifier                            res/vclausify_rel
% 2.89/1.01  --clausifier_options                    --mode clausify
% 2.89/1.01  --stdin                                 false
% 2.89/1.01  --stats_out                             all
% 2.89/1.01  
% 2.89/1.01  ------ General Options
% 2.89/1.01  
% 2.89/1.01  --fof                                   false
% 2.89/1.01  --time_out_real                         305.
% 2.89/1.01  --time_out_virtual                      -1.
% 2.89/1.01  --symbol_type_check                     false
% 2.89/1.01  --clausify_out                          false
% 2.89/1.01  --sig_cnt_out                           false
% 2.89/1.01  --trig_cnt_out                          false
% 2.89/1.01  --trig_cnt_out_tolerance                1.
% 2.89/1.01  --trig_cnt_out_sk_spl                   false
% 2.89/1.01  --abstr_cl_out                          false
% 2.89/1.01  
% 2.89/1.01  ------ Global Options
% 2.89/1.01  
% 2.89/1.01  --schedule                              default
% 2.89/1.01  --add_important_lit                     false
% 2.89/1.01  --prop_solver_per_cl                    1000
% 2.89/1.01  --min_unsat_core                        false
% 2.89/1.01  --soft_assumptions                      false
% 2.89/1.01  --soft_lemma_size                       3
% 2.89/1.01  --prop_impl_unit_size                   0
% 2.89/1.01  --prop_impl_unit                        []
% 2.89/1.01  --share_sel_clauses                     true
% 2.89/1.01  --reset_solvers                         false
% 2.89/1.01  --bc_imp_inh                            [conj_cone]
% 2.89/1.01  --conj_cone_tolerance                   3.
% 2.89/1.01  --extra_neg_conj                        none
% 2.89/1.01  --large_theory_mode                     true
% 2.89/1.01  --prolific_symb_bound                   200
% 2.89/1.01  --lt_threshold                          2000
% 2.89/1.01  --clause_weak_htbl                      true
% 2.89/1.01  --gc_record_bc_elim                     false
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing Options
% 2.89/1.01  
% 2.89/1.01  --preprocessing_flag                    true
% 2.89/1.01  --time_out_prep_mult                    0.1
% 2.89/1.01  --splitting_mode                        input
% 2.89/1.01  --splitting_grd                         true
% 2.89/1.01  --splitting_cvd                         false
% 2.89/1.01  --splitting_cvd_svl                     false
% 2.89/1.01  --splitting_nvd                         32
% 2.89/1.01  --sub_typing                            true
% 2.89/1.01  --prep_gs_sim                           true
% 2.89/1.01  --prep_unflatten                        true
% 2.89/1.01  --prep_res_sim                          true
% 2.89/1.01  --prep_upred                            true
% 2.89/1.01  --prep_sem_filter                       exhaustive
% 2.89/1.01  --prep_sem_filter_out                   false
% 2.89/1.01  --pred_elim                             true
% 2.89/1.01  --res_sim_input                         true
% 2.89/1.01  --eq_ax_congr_red                       true
% 2.89/1.01  --pure_diseq_elim                       true
% 2.89/1.01  --brand_transform                       false
% 2.89/1.01  --non_eq_to_eq                          false
% 2.89/1.01  --prep_def_merge                        true
% 2.89/1.01  --prep_def_merge_prop_impl              false
% 2.89/1.01  --prep_def_merge_mbd                    true
% 2.89/1.01  --prep_def_merge_tr_red                 false
% 2.89/1.01  --prep_def_merge_tr_cl                  false
% 2.89/1.01  --smt_preprocessing                     true
% 2.89/1.01  --smt_ac_axioms                         fast
% 2.89/1.01  --preprocessed_out                      false
% 2.89/1.01  --preprocessed_stats                    false
% 2.89/1.01  
% 2.89/1.01  ------ Abstraction refinement Options
% 2.89/1.01  
% 2.89/1.01  --abstr_ref                             []
% 2.89/1.01  --abstr_ref_prep                        false
% 2.89/1.01  --abstr_ref_until_sat                   false
% 2.89/1.01  --abstr_ref_sig_restrict                funpre
% 2.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.01  --abstr_ref_under                       []
% 2.89/1.01  
% 2.89/1.01  ------ SAT Options
% 2.89/1.01  
% 2.89/1.01  --sat_mode                              false
% 2.89/1.01  --sat_fm_restart_options                ""
% 2.89/1.01  --sat_gr_def                            false
% 2.89/1.01  --sat_epr_types                         true
% 2.89/1.01  --sat_non_cyclic_types                  false
% 2.89/1.01  --sat_finite_models                     false
% 2.89/1.01  --sat_fm_lemmas                         false
% 2.89/1.01  --sat_fm_prep                           false
% 2.89/1.01  --sat_fm_uc_incr                        true
% 2.89/1.01  --sat_out_model                         small
% 2.89/1.01  --sat_out_clauses                       false
% 2.89/1.01  
% 2.89/1.01  ------ QBF Options
% 2.89/1.01  
% 2.89/1.01  --qbf_mode                              false
% 2.89/1.01  --qbf_elim_univ                         false
% 2.89/1.01  --qbf_dom_inst                          none
% 2.89/1.01  --qbf_dom_pre_inst                      false
% 2.89/1.01  --qbf_sk_in                             false
% 2.89/1.01  --qbf_pred_elim                         true
% 2.89/1.01  --qbf_split                             512
% 2.89/1.01  
% 2.89/1.01  ------ BMC1 Options
% 2.89/1.01  
% 2.89/1.01  --bmc1_incremental                      false
% 2.89/1.01  --bmc1_axioms                           reachable_all
% 2.89/1.01  --bmc1_min_bound                        0
% 2.89/1.01  --bmc1_max_bound                        -1
% 2.89/1.01  --bmc1_max_bound_default                -1
% 2.89/1.01  --bmc1_symbol_reachability              true
% 2.89/1.01  --bmc1_property_lemmas                  false
% 2.89/1.01  --bmc1_k_induction                      false
% 2.89/1.01  --bmc1_non_equiv_states                 false
% 2.89/1.01  --bmc1_deadlock                         false
% 2.89/1.01  --bmc1_ucm                              false
% 2.89/1.01  --bmc1_add_unsat_core                   none
% 2.89/1.01  --bmc1_unsat_core_children              false
% 2.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.01  --bmc1_out_stat                         full
% 2.89/1.01  --bmc1_ground_init                      false
% 2.89/1.01  --bmc1_pre_inst_next_state              false
% 2.89/1.01  --bmc1_pre_inst_state                   false
% 2.89/1.01  --bmc1_pre_inst_reach_state             false
% 2.89/1.01  --bmc1_out_unsat_core                   false
% 2.89/1.01  --bmc1_aig_witness_out                  false
% 2.89/1.01  --bmc1_verbose                          false
% 2.89/1.01  --bmc1_dump_clauses_tptp                false
% 2.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.01  --bmc1_dump_file                        -
% 2.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.01  --bmc1_ucm_extend_mode                  1
% 2.89/1.01  --bmc1_ucm_init_mode                    2
% 2.89/1.01  --bmc1_ucm_cone_mode                    none
% 2.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.01  --bmc1_ucm_relax_model                  4
% 2.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.01  --bmc1_ucm_layered_model                none
% 2.89/1.01  --bmc1_ucm_max_lemma_size               10
% 2.89/1.01  
% 2.89/1.01  ------ AIG Options
% 2.89/1.01  
% 2.89/1.01  --aig_mode                              false
% 2.89/1.01  
% 2.89/1.01  ------ Instantiation Options
% 2.89/1.01  
% 2.89/1.01  --instantiation_flag                    true
% 2.89/1.01  --inst_sos_flag                         false
% 2.89/1.01  --inst_sos_phase                        true
% 2.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel_side                     num_symb
% 2.89/1.01  --inst_solver_per_active                1400
% 2.89/1.01  --inst_solver_calls_frac                1.
% 2.89/1.01  --inst_passive_queue_type               priority_queues
% 2.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.01  --inst_passive_queues_freq              [25;2]
% 2.89/1.01  --inst_dismatching                      true
% 2.89/1.01  --inst_eager_unprocessed_to_passive     true
% 2.89/1.01  --inst_prop_sim_given                   true
% 2.89/1.01  --inst_prop_sim_new                     false
% 2.89/1.01  --inst_subs_new                         false
% 2.89/1.01  --inst_eq_res_simp                      false
% 2.89/1.01  --inst_subs_given                       false
% 2.89/1.01  --inst_orphan_elimination               true
% 2.89/1.01  --inst_learning_loop_flag               true
% 2.89/1.01  --inst_learning_start                   3000
% 2.89/1.01  --inst_learning_factor                  2
% 2.89/1.01  --inst_start_prop_sim_after_learn       3
% 2.89/1.01  --inst_sel_renew                        solver
% 2.89/1.01  --inst_lit_activity_flag                true
% 2.89/1.01  --inst_restr_to_given                   false
% 2.89/1.01  --inst_activity_threshold               500
% 2.89/1.01  --inst_out_proof                        true
% 2.89/1.01  
% 2.89/1.01  ------ Resolution Options
% 2.89/1.01  
% 2.89/1.01  --resolution_flag                       true
% 2.89/1.01  --res_lit_sel                           adaptive
% 2.89/1.01  --res_lit_sel_side                      none
% 2.89/1.01  --res_ordering                          kbo
% 2.89/1.01  --res_to_prop_solver                    active
% 2.89/1.01  --res_prop_simpl_new                    false
% 2.89/1.01  --res_prop_simpl_given                  true
% 2.89/1.01  --res_passive_queue_type                priority_queues
% 2.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.01  --res_passive_queues_freq               [15;5]
% 2.89/1.01  --res_forward_subs                      full
% 2.89/1.01  --res_backward_subs                     full
% 2.89/1.01  --res_forward_subs_resolution           true
% 2.89/1.01  --res_backward_subs_resolution          true
% 2.89/1.01  --res_orphan_elimination                true
% 2.89/1.01  --res_time_limit                        2.
% 2.89/1.01  --res_out_proof                         true
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Options
% 2.89/1.01  
% 2.89/1.01  --superposition_flag                    true
% 2.89/1.01  --sup_passive_queue_type                priority_queues
% 2.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.01  --demod_completeness_check              fast
% 2.89/1.01  --demod_use_ground                      true
% 2.89/1.01  --sup_to_prop_solver                    passive
% 2.89/1.01  --sup_prop_simpl_new                    true
% 2.89/1.01  --sup_prop_simpl_given                  true
% 2.89/1.01  --sup_fun_splitting                     false
% 2.89/1.01  --sup_smt_interval                      50000
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Simplification Setup
% 2.89/1.01  
% 2.89/1.01  --sup_indices_passive                   []
% 2.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_full_bw                           [BwDemod]
% 2.89/1.01  --sup_immed_triv                        [TrivRules]
% 2.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_immed_bw_main                     []
% 2.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  
% 2.89/1.01  ------ Combination Options
% 2.89/1.01  
% 2.89/1.01  --comb_res_mult                         3
% 2.89/1.01  --comb_sup_mult                         2
% 2.89/1.01  --comb_inst_mult                        10
% 2.89/1.01  
% 2.89/1.01  ------ Debug Options
% 2.89/1.01  
% 2.89/1.01  --dbg_backtrace                         false
% 2.89/1.01  --dbg_dump_prop_clauses                 false
% 2.89/1.01  --dbg_dump_prop_clauses_file            -
% 2.89/1.01  --dbg_out_stat                          false
% 2.89/1.01  ------ Parsing...
% 2.89/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/1.01  ------ Proving...
% 2.89/1.01  ------ Problem Properties 
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  clauses                                 28
% 2.89/1.01  conjectures                             3
% 2.89/1.01  EPR                                     5
% 2.89/1.01  Horn                                    21
% 2.89/1.01  unary                                   10
% 2.89/1.01  binary                                  10
% 2.89/1.01  lits                                    56
% 2.89/1.01  lits eq                                 23
% 2.89/1.01  fd_pure                                 0
% 2.89/1.01  fd_pseudo                               0
% 2.89/1.01  fd_cond                                 3
% 2.89/1.01  fd_pseudo_cond                          0
% 2.89/1.01  AC symbols                              0
% 2.89/1.01  
% 2.89/1.01  ------ Schedule dynamic 5 is on 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  ------ 
% 2.89/1.01  Current options:
% 2.89/1.01  ------ 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options
% 2.89/1.01  
% 2.89/1.01  --out_options                           all
% 2.89/1.01  --tptp_safe_out                         true
% 2.89/1.01  --problem_path                          ""
% 2.89/1.01  --include_path                          ""
% 2.89/1.01  --clausifier                            res/vclausify_rel
% 2.89/1.01  --clausifier_options                    --mode clausify
% 2.89/1.01  --stdin                                 false
% 2.89/1.01  --stats_out                             all
% 2.89/1.01  
% 2.89/1.01  ------ General Options
% 2.89/1.01  
% 2.89/1.01  --fof                                   false
% 2.89/1.01  --time_out_real                         305.
% 2.89/1.01  --time_out_virtual                      -1.
% 2.89/1.01  --symbol_type_check                     false
% 2.89/1.01  --clausify_out                          false
% 2.89/1.01  --sig_cnt_out                           false
% 2.89/1.01  --trig_cnt_out                          false
% 2.89/1.01  --trig_cnt_out_tolerance                1.
% 2.89/1.01  --trig_cnt_out_sk_spl                   false
% 2.89/1.01  --abstr_cl_out                          false
% 2.89/1.01  
% 2.89/1.01  ------ Global Options
% 2.89/1.01  
% 2.89/1.01  --schedule                              default
% 2.89/1.01  --add_important_lit                     false
% 2.89/1.01  --prop_solver_per_cl                    1000
% 2.89/1.01  --min_unsat_core                        false
% 2.89/1.01  --soft_assumptions                      false
% 2.89/1.01  --soft_lemma_size                       3
% 2.89/1.01  --prop_impl_unit_size                   0
% 2.89/1.01  --prop_impl_unit                        []
% 2.89/1.01  --share_sel_clauses                     true
% 2.89/1.01  --reset_solvers                         false
% 2.89/1.01  --bc_imp_inh                            [conj_cone]
% 2.89/1.01  --conj_cone_tolerance                   3.
% 2.89/1.01  --extra_neg_conj                        none
% 2.89/1.01  --large_theory_mode                     true
% 2.89/1.01  --prolific_symb_bound                   200
% 2.89/1.01  --lt_threshold                          2000
% 2.89/1.01  --clause_weak_htbl                      true
% 2.89/1.01  --gc_record_bc_elim                     false
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing Options
% 2.89/1.01  
% 2.89/1.01  --preprocessing_flag                    true
% 2.89/1.01  --time_out_prep_mult                    0.1
% 2.89/1.01  --splitting_mode                        input
% 2.89/1.01  --splitting_grd                         true
% 2.89/1.01  --splitting_cvd                         false
% 2.89/1.01  --splitting_cvd_svl                     false
% 2.89/1.01  --splitting_nvd                         32
% 2.89/1.01  --sub_typing                            true
% 2.89/1.01  --prep_gs_sim                           true
% 2.89/1.01  --prep_unflatten                        true
% 2.89/1.01  --prep_res_sim                          true
% 2.89/1.01  --prep_upred                            true
% 2.89/1.01  --prep_sem_filter                       exhaustive
% 2.89/1.01  --prep_sem_filter_out                   false
% 2.89/1.01  --pred_elim                             true
% 2.89/1.01  --res_sim_input                         true
% 2.89/1.01  --eq_ax_congr_red                       true
% 2.89/1.01  --pure_diseq_elim                       true
% 2.89/1.01  --brand_transform                       false
% 2.89/1.01  --non_eq_to_eq                          false
% 2.89/1.01  --prep_def_merge                        true
% 2.89/1.01  --prep_def_merge_prop_impl              false
% 2.89/1.01  --prep_def_merge_mbd                    true
% 2.89/1.01  --prep_def_merge_tr_red                 false
% 2.89/1.01  --prep_def_merge_tr_cl                  false
% 2.89/1.01  --smt_preprocessing                     true
% 2.89/1.01  --smt_ac_axioms                         fast
% 2.89/1.01  --preprocessed_out                      false
% 2.89/1.01  --preprocessed_stats                    false
% 2.89/1.01  
% 2.89/1.01  ------ Abstraction refinement Options
% 2.89/1.01  
% 2.89/1.01  --abstr_ref                             []
% 2.89/1.01  --abstr_ref_prep                        false
% 2.89/1.01  --abstr_ref_until_sat                   false
% 2.89/1.01  --abstr_ref_sig_restrict                funpre
% 2.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.01  --abstr_ref_under                       []
% 2.89/1.01  
% 2.89/1.01  ------ SAT Options
% 2.89/1.01  
% 2.89/1.01  --sat_mode                              false
% 2.89/1.01  --sat_fm_restart_options                ""
% 2.89/1.01  --sat_gr_def                            false
% 2.89/1.01  --sat_epr_types                         true
% 2.89/1.01  --sat_non_cyclic_types                  false
% 2.89/1.01  --sat_finite_models                     false
% 2.89/1.01  --sat_fm_lemmas                         false
% 2.89/1.01  --sat_fm_prep                           false
% 2.89/1.01  --sat_fm_uc_incr                        true
% 2.89/1.01  --sat_out_model                         small
% 2.89/1.01  --sat_out_clauses                       false
% 2.89/1.01  
% 2.89/1.01  ------ QBF Options
% 2.89/1.01  
% 2.89/1.01  --qbf_mode                              false
% 2.89/1.01  --qbf_elim_univ                         false
% 2.89/1.01  --qbf_dom_inst                          none
% 2.89/1.01  --qbf_dom_pre_inst                      false
% 2.89/1.01  --qbf_sk_in                             false
% 2.89/1.01  --qbf_pred_elim                         true
% 2.89/1.01  --qbf_split                             512
% 2.89/1.01  
% 2.89/1.01  ------ BMC1 Options
% 2.89/1.01  
% 2.89/1.01  --bmc1_incremental                      false
% 2.89/1.01  --bmc1_axioms                           reachable_all
% 2.89/1.01  --bmc1_min_bound                        0
% 2.89/1.01  --bmc1_max_bound                        -1
% 2.89/1.01  --bmc1_max_bound_default                -1
% 2.89/1.01  --bmc1_symbol_reachability              true
% 2.89/1.01  --bmc1_property_lemmas                  false
% 2.89/1.01  --bmc1_k_induction                      false
% 2.89/1.01  --bmc1_non_equiv_states                 false
% 2.89/1.01  --bmc1_deadlock                         false
% 2.89/1.01  --bmc1_ucm                              false
% 2.89/1.01  --bmc1_add_unsat_core                   none
% 2.89/1.01  --bmc1_unsat_core_children              false
% 2.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.01  --bmc1_out_stat                         full
% 2.89/1.01  --bmc1_ground_init                      false
% 2.89/1.01  --bmc1_pre_inst_next_state              false
% 2.89/1.01  --bmc1_pre_inst_state                   false
% 2.89/1.01  --bmc1_pre_inst_reach_state             false
% 2.89/1.01  --bmc1_out_unsat_core                   false
% 2.89/1.01  --bmc1_aig_witness_out                  false
% 2.89/1.01  --bmc1_verbose                          false
% 2.89/1.01  --bmc1_dump_clauses_tptp                false
% 2.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.01  --bmc1_dump_file                        -
% 2.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.01  --bmc1_ucm_extend_mode                  1
% 2.89/1.01  --bmc1_ucm_init_mode                    2
% 2.89/1.01  --bmc1_ucm_cone_mode                    none
% 2.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.01  --bmc1_ucm_relax_model                  4
% 2.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.01  --bmc1_ucm_layered_model                none
% 2.89/1.01  --bmc1_ucm_max_lemma_size               10
% 2.89/1.01  
% 2.89/1.01  ------ AIG Options
% 2.89/1.01  
% 2.89/1.01  --aig_mode                              false
% 2.89/1.01  
% 2.89/1.01  ------ Instantiation Options
% 2.89/1.01  
% 2.89/1.01  --instantiation_flag                    true
% 2.89/1.01  --inst_sos_flag                         false
% 2.89/1.01  --inst_sos_phase                        true
% 2.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel_side                     none
% 2.89/1.01  --inst_solver_per_active                1400
% 2.89/1.01  --inst_solver_calls_frac                1.
% 2.89/1.01  --inst_passive_queue_type               priority_queues
% 2.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.01  --inst_passive_queues_freq              [25;2]
% 2.89/1.01  --inst_dismatching                      true
% 2.89/1.01  --inst_eager_unprocessed_to_passive     true
% 2.89/1.01  --inst_prop_sim_given                   true
% 2.89/1.01  --inst_prop_sim_new                     false
% 2.89/1.01  --inst_subs_new                         false
% 2.89/1.01  --inst_eq_res_simp                      false
% 2.89/1.01  --inst_subs_given                       false
% 2.89/1.01  --inst_orphan_elimination               true
% 2.89/1.01  --inst_learning_loop_flag               true
% 2.89/1.01  --inst_learning_start                   3000
% 2.89/1.01  --inst_learning_factor                  2
% 2.89/1.01  --inst_start_prop_sim_after_learn       3
% 2.89/1.01  --inst_sel_renew                        solver
% 2.89/1.01  --inst_lit_activity_flag                true
% 2.89/1.01  --inst_restr_to_given                   false
% 2.89/1.01  --inst_activity_threshold               500
% 2.89/1.01  --inst_out_proof                        true
% 2.89/1.01  
% 2.89/1.01  ------ Resolution Options
% 2.89/1.01  
% 2.89/1.01  --resolution_flag                       false
% 2.89/1.01  --res_lit_sel                           adaptive
% 2.89/1.01  --res_lit_sel_side                      none
% 2.89/1.01  --res_ordering                          kbo
% 2.89/1.01  --res_to_prop_solver                    active
% 2.89/1.01  --res_prop_simpl_new                    false
% 2.89/1.01  --res_prop_simpl_given                  true
% 2.89/1.01  --res_passive_queue_type                priority_queues
% 2.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.01  --res_passive_queues_freq               [15;5]
% 2.89/1.01  --res_forward_subs                      full
% 2.89/1.01  --res_backward_subs                     full
% 2.89/1.01  --res_forward_subs_resolution           true
% 2.89/1.01  --res_backward_subs_resolution          true
% 2.89/1.01  --res_orphan_elimination                true
% 2.89/1.01  --res_time_limit                        2.
% 2.89/1.01  --res_out_proof                         true
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Options
% 2.89/1.01  
% 2.89/1.01  --superposition_flag                    true
% 2.89/1.01  --sup_passive_queue_type                priority_queues
% 2.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.01  --demod_completeness_check              fast
% 2.89/1.01  --demod_use_ground                      true
% 2.89/1.01  --sup_to_prop_solver                    passive
% 2.89/1.01  --sup_prop_simpl_new                    true
% 2.89/1.01  --sup_prop_simpl_given                  true
% 2.89/1.01  --sup_fun_splitting                     false
% 2.89/1.01  --sup_smt_interval                      50000
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Simplification Setup
% 2.89/1.01  
% 2.89/1.01  --sup_indices_passive                   []
% 2.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_full_bw                           [BwDemod]
% 2.89/1.01  --sup_immed_triv                        [TrivRules]
% 2.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_immed_bw_main                     []
% 2.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  
% 2.89/1.01  ------ Combination Options
% 2.89/1.01  
% 2.89/1.01  --comb_res_mult                         3
% 2.89/1.01  --comb_sup_mult                         2
% 2.89/1.01  --comb_inst_mult                        10
% 2.89/1.01  
% 2.89/1.01  ------ Debug Options
% 2.89/1.01  
% 2.89/1.01  --dbg_backtrace                         false
% 2.89/1.01  --dbg_dump_prop_clauses                 false
% 2.89/1.01  --dbg_dump_prop_clauses_file            -
% 2.89/1.01  --dbg_out_stat                          false
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  ------ Proving...
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  % SZS status Theorem for theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  fof(f18,conjecture,(
% 2.89/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f19,negated_conjecture,(
% 2.89/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.89/1.01    inference(negated_conjecture,[],[f18])).
% 2.89/1.01  
% 2.89/1.01  fof(f20,plain,(
% 2.89/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.89/1.01    inference(pure_predicate_removal,[],[f19])).
% 2.89/1.01  
% 2.89/1.01  fof(f33,plain,(
% 2.89/1.01    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 2.89/1.01    inference(ennf_transformation,[],[f20])).
% 2.89/1.01  
% 2.89/1.01  fof(f34,plain,(
% 2.89/1.01    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 2.89/1.01    inference(flattening,[],[f33])).
% 2.89/1.01  
% 2.89/1.01  fof(f43,plain,(
% 2.89/1.01    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3))),
% 2.89/1.01    introduced(choice_axiom,[])).
% 2.89/1.01  
% 2.89/1.01  fof(f44,plain,(
% 2.89/1.01    (~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3)),
% 2.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f43])).
% 2.89/1.01  
% 2.89/1.01  fof(f76,plain,(
% 2.89/1.01    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f17,axiom,(
% 2.89/1.01    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f74,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f17])).
% 2.89/1.01  
% 2.89/1.01  fof(f81,plain,(
% 2.89/1.01    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 2.89/1.01    inference(definition_unfolding,[],[f76,f74])).
% 2.89/1.01  
% 2.89/1.01  fof(f16,axiom,(
% 2.89/1.01    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f21,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 2.89/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.89/1.01  
% 2.89/1.01  fof(f32,plain,(
% 2.89/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.89/1.01    inference(ennf_transformation,[],[f21])).
% 2.89/1.01  
% 2.89/1.01  fof(f73,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f32])).
% 2.89/1.01  
% 2.89/1.01  fof(f79,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.89/1.01    inference(definition_unfolding,[],[f73,f74])).
% 2.89/1.01  
% 2.89/1.01  fof(f8,axiom,(
% 2.89/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f41,plain,(
% 2.89/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.89/1.01    inference(nnf_transformation,[],[f8])).
% 2.89/1.01  
% 2.89/1.01  fof(f55,plain,(
% 2.89/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f41])).
% 2.89/1.01  
% 2.89/1.01  fof(f10,axiom,(
% 2.89/1.01    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f24,plain,(
% 2.89/1.01    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.89/1.01    inference(ennf_transformation,[],[f10])).
% 2.89/1.01  
% 2.89/1.01  fof(f59,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.89/1.01    inference(cnf_transformation,[],[f24])).
% 2.89/1.01  
% 2.89/1.01  fof(f11,axiom,(
% 2.89/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f25,plain,(
% 2.89/1.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(ennf_transformation,[],[f11])).
% 2.89/1.01  
% 2.89/1.01  fof(f26,plain,(
% 2.89/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(flattening,[],[f25])).
% 2.89/1.01  
% 2.89/1.01  fof(f61,plain,(
% 2.89/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f26])).
% 2.89/1.01  
% 2.89/1.01  fof(f9,axiom,(
% 2.89/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f57,plain,(
% 2.89/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f9])).
% 2.89/1.01  
% 2.89/1.01  fof(f75,plain,(
% 2.89/1.01    v1_relat_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f72,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f32])).
% 2.89/1.01  
% 2.89/1.01  fof(f80,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.89/1.01    inference(definition_unfolding,[],[f72,f74])).
% 2.89/1.01  
% 2.89/1.01  fof(f14,axiom,(
% 2.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f28,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(ennf_transformation,[],[f14])).
% 2.89/1.01  
% 2.89/1.01  fof(f29,plain,(
% 2.89/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(flattening,[],[f28])).
% 2.89/1.01  
% 2.89/1.01  fof(f42,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(nnf_transformation,[],[f29])).
% 2.89/1.01  
% 2.89/1.01  fof(f65,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f42])).
% 2.89/1.01  
% 2.89/1.01  fof(f13,axiom,(
% 2.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f27,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(ennf_transformation,[],[f13])).
% 2.89/1.01  
% 2.89/1.01  fof(f64,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f27])).
% 2.89/1.01  
% 2.89/1.01  fof(f77,plain,(
% 2.89/1.01    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f7,axiom,(
% 2.89/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f39,plain,(
% 2.89/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/1.01    inference(nnf_transformation,[],[f7])).
% 2.89/1.01  
% 2.89/1.01  fof(f40,plain,(
% 2.89/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/1.01    inference(flattening,[],[f39])).
% 2.89/1.01  
% 2.89/1.01  fof(f53,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.89/1.01    inference(cnf_transformation,[],[f40])).
% 2.89/1.01  
% 2.89/1.01  fof(f83,plain,(
% 2.89/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.89/1.01    inference(equality_resolution,[],[f53])).
% 2.89/1.01  
% 2.89/1.01  fof(f5,axiom,(
% 2.89/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f23,plain,(
% 2.89/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.89/1.01    inference(ennf_transformation,[],[f5])).
% 2.89/1.01  
% 2.89/1.01  fof(f50,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f23])).
% 2.89/1.01  
% 2.89/1.01  fof(f1,axiom,(
% 2.89/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f45,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f1])).
% 2.89/1.01  
% 2.89/1.01  fof(f6,axiom,(
% 2.89/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f51,plain,(
% 2.89/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f6])).
% 2.89/1.01  
% 2.89/1.01  fof(f54,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.89/1.01    inference(cnf_transformation,[],[f40])).
% 2.89/1.01  
% 2.89/1.01  fof(f82,plain,(
% 2.89/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.89/1.01    inference(equality_resolution,[],[f54])).
% 2.89/1.01  
% 2.89/1.01  fof(f12,axiom,(
% 2.89/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f63,plain,(
% 2.89/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.89/1.01    inference(cnf_transformation,[],[f12])).
% 2.89/1.01  
% 2.89/1.01  fof(f62,plain,(
% 2.89/1.01    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.89/1.01    inference(cnf_transformation,[],[f12])).
% 2.89/1.01  
% 2.89/1.01  fof(f15,axiom,(
% 2.89/1.01    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f30,plain,(
% 2.89/1.01    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.89/1.01    inference(ennf_transformation,[],[f15])).
% 2.89/1.01  
% 2.89/1.01  fof(f31,plain,(
% 2.89/1.01    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.89/1.01    inference(flattening,[],[f30])).
% 2.89/1.01  
% 2.89/1.01  fof(f71,plain,(
% 2.89/1.01    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f31])).
% 2.89/1.01  
% 2.89/1.01  fof(f78,plain,(
% 2.89/1.01    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.89/1.01    inference(definition_unfolding,[],[f71,f74])).
% 2.89/1.01  
% 2.89/1.01  fof(f2,axiom,(
% 2.89/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f35,plain,(
% 2.89/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.89/1.01    inference(nnf_transformation,[],[f2])).
% 2.89/1.01  
% 2.89/1.01  fof(f36,plain,(
% 2.89/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.89/1.01    inference(rectify,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f37,plain,(
% 2.89/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.89/1.01    introduced(choice_axiom,[])).
% 2.89/1.01  
% 2.89/1.01  fof(f38,plain,(
% 2.89/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.89/1.01  
% 2.89/1.01  fof(f46,plain,(
% 2.89/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f38])).
% 2.89/1.01  
% 2.89/1.01  fof(f4,axiom,(
% 2.89/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f22,plain,(
% 2.89/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.89/1.01    inference(ennf_transformation,[],[f4])).
% 2.89/1.01  
% 2.89/1.01  fof(f49,plain,(
% 2.89/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f22])).
% 2.89/1.01  
% 2.89/1.01  fof(f3,axiom,(
% 2.89/1.01    v1_xboole_0(k1_xboole_0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f48,plain,(
% 2.89/1.01    v1_xboole_0(k1_xboole_0)),
% 2.89/1.01    inference(cnf_transformation,[],[f3])).
% 2.89/1.01  
% 2.89/1.01  cnf(c_30,negated_conjecture,
% 2.89/1.01      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
% 2.89/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1860,plain,
% 2.89/1.01      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_27,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.89/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1862,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.89/1.01      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3186,plain,
% 2.89/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_1860,c_1862]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_11,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.89/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1868,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.89/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3453,plain,
% 2.89/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3186,c_1868]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_13,plain,
% 2.89/1.01      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 2.89/1.01      | k1_xboole_0 = X0
% 2.89/1.01      | k1_xboole_0 = X1 ),
% 2.89/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_15,plain,
% 2.89/1.01      ( ~ r1_tarski(X0,X1)
% 2.89/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.89/1.01      | ~ v1_relat_1(X1)
% 2.89/1.01      | ~ v1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1866,plain,
% 2.89/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.89/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.89/1.01      | v1_relat_1(X1) != iProver_top
% 2.89/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3827,plain,
% 2.89/1.01      ( k1_xboole_0 = X0
% 2.89/1.01      | k1_xboole_0 = X1
% 2.89/1.01      | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
% 2.89/1.01      | r1_tarski(k2_relat_1(X2),X0) = iProver_top
% 2.89/1.01      | v1_relat_1(X2) != iProver_top
% 2.89/1.01      | v1_relat_1(k2_zfmisc_1(X1,X0)) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_13,c_1866]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_12,plain,
% 2.89/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.89/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1867,plain,
% 2.89/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5389,plain,
% 2.89/1.01      ( k1_xboole_0 = X0
% 2.89/1.01      | k1_xboole_0 = X1
% 2.89/1.01      | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
% 2.89/1.01      | r1_tarski(k2_relat_1(X2),X0) = iProver_top
% 2.89/1.01      | v1_relat_1(X2) != iProver_top ),
% 2.89/1.01      inference(forward_subsumption_resolution,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_3827,c_1867]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5392,plain,
% 2.89/1.01      ( sK1 = k1_xboole_0
% 2.89/1.01      | sK2 = k1_xboole_0
% 2.89/1.01      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3453,c_5389]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_31,negated_conjecture,
% 2.89/1.01      ( v1_relat_1(sK3) ),
% 2.89/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_28,plain,
% 2.89/1.01      ( v1_funct_2(X0,X1,X2)
% 2.89/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.89/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_25,plain,
% 2.89/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_720,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(resolution,[status(thm)],[c_28,c_25]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_415,plain,
% 2.89/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(resolution,[status(thm)],[c_27,c_25]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_419,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_415,c_28]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_724,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_720,c_28,c_415]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1858,plain,
% 2.89/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.89/1.01      | k1_xboole_0 = X1
% 2.89/1.01      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3050,plain,
% 2.89/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_1860,c_1858]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_19,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1864,plain,
% 2.89/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.89/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3454,plain,
% 2.89/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3186,c_1864]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3518,plain,
% 2.89/1.01      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3050,c_3454]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_29,negated_conjecture,
% 2.89/1.01      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1 ),
% 2.89/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1861,plain,
% 2.89/1.01      ( k1_relat_1(sK3) != sK1
% 2.89/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3593,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3518,c_1861]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3633,plain,
% 2.89/1.01      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3593]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5408,plain,
% 2.89/1.01      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.89/1.01      | ~ v1_relat_1(sK3)
% 2.89/1.01      | sK1 = k1_xboole_0
% 2.89/1.01      | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5392]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5509,plain,
% 2.89/1.01      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_5392,c_31,c_3633,c_5408]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5530,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_5509,c_3453]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_8,plain,
% 2.89/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5556,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5530,c_8]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5,plain,
% 2.89/1.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.89/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1871,plain,
% 2.89/1.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_6028,plain,
% 2.89/1.01      ( k2_xboole_0(sK3,k1_xboole_0) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_5556,c_1871]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_0,plain,
% 2.89/1.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_6,plain,
% 2.89/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1870,plain,
% 2.89/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2543,plain,
% 2.89/1.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_1870,c_1871]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2585,plain,
% 2.89/1.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_0,c_2543]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_6044,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_6028,c_2585]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3516,plain,
% 2.89/1.01      ( k2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2)) = k2_zfmisc_1(sK1,sK2) ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3453,c_1871]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7198,plain,
% 2.89/1.01      ( k2_xboole_0(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = k2_zfmisc_1(sK1,sK2)
% 2.89/1.01      | sK3 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_6044,c_3516]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7,plain,
% 2.89/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7239,plain,
% 2.89/1.01      ( k2_zfmisc_1(sK1,sK2) = sK3 | sK3 = k1_xboole_0 ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_7198,c_7,c_2585]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7283,plain,
% 2.89/1.01      ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3 | sK3 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_6044,c_7239]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7330,plain,
% 2.89/1.01      ( sK3 = k1_xboole_0 ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_7283,c_7]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7448,plain,
% 2.89/1.02      ( k1_relat_1(k1_xboole_0) != sK1
% 2.89/1.02      | r1_tarski(k2_relat_1(k1_xboole_0),sK2) != iProver_top ),
% 2.89/1.02      inference(demodulation,[status(thm)],[c_7330,c_1861]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_17,plain,
% 2.89/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_18,plain,
% 2.89/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_7455,plain,
% 2.89/1.02      ( sK1 != k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.89/1.02      inference(light_normalisation,[status(thm)],[c_7448,c_17,c_18]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_2452,plain,
% 2.89/1.02      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_2455,plain,
% 2.89/1.02      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.89/1.02      inference(predicate_to_equality,[status(thm)],[c_2452]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_7630,plain,
% 2.89/1.02      ( sK1 != k1_xboole_0 ),
% 2.89/1.02      inference(global_propositional_subsumption,
% 2.89/1.02                [status(thm)],
% 2.89/1.02                [c_7455,c_2455]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_7633,plain,
% 2.89/1.02      ( sK2 = k1_xboole_0 ),
% 2.89/1.02      inference(superposition,[status(thm)],[c_5509,c_7630]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_26,plain,
% 2.89/1.02      ( ~ v1_xboole_0(X0)
% 2.89/1.02      | v1_xboole_0(X1)
% 2.89/1.02      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 2.89/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_1863,plain,
% 2.89/1.02      ( v1_xboole_0(X0) != iProver_top
% 2.89/1.02      | v1_xboole_0(X1) = iProver_top
% 2.89/1.02      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 2.89/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_2,plain,
% 2.89/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.89/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_1874,plain,
% 2.89/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.89/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.89/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_2736,plain,
% 2.89/1.02      ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
% 2.89/1.02      inference(superposition,[status(thm)],[c_1860,c_1874]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3200,plain,
% 2.89/1.02      ( v1_xboole_0(sK1) = iProver_top
% 2.89/1.02      | v1_xboole_0(sK2) != iProver_top ),
% 2.89/1.02      inference(superposition,[status(thm)],[c_1863,c_2736]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_7682,plain,
% 2.89/1.02      ( v1_xboole_0(sK1) = iProver_top
% 2.89/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.89/1.02      inference(demodulation,[status(thm)],[c_7633,c_3200]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_1325,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3388,plain,
% 2.89/1.02      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_6812,plain,
% 2.89/1.02      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_3388]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_6813,plain,
% 2.89/1.02      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_6812]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_4,plain,
% 2.89/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.89/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3414,plain,
% 2.89/1.02      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3415,plain,
% 2.89/1.02      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.89/1.02      inference(predicate_to_equality,[status(thm)],[c_3414]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_1324,plain,( X0 = X0 ),theory(equality) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3386,plain,
% 2.89/1.02      ( sK1 = sK1 ),
% 2.89/1.02      inference(instantiation,[status(thm)],[c_1324]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_3,plain,
% 2.89/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.89/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(c_91,plain,
% 2.89/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.89/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.89/1.02  
% 2.89/1.02  cnf(contradiction,plain,
% 2.89/1.02      ( $false ),
% 2.89/1.02      inference(minisat,
% 2.89/1.02                [status(thm)],
% 2.89/1.02                [c_7682,c_7455,c_6813,c_3415,c_3386,c_2455,c_91]) ).
% 2.89/1.02  
% 2.89/1.02  
% 2.89/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/1.02  
% 2.89/1.02  ------                               Statistics
% 2.89/1.02  
% 2.89/1.02  ------ General
% 2.89/1.02  
% 2.89/1.02  abstr_ref_over_cycles:                  0
% 2.89/1.02  abstr_ref_under_cycles:                 0
% 2.89/1.02  gc_basic_clause_elim:                   0
% 2.89/1.02  forced_gc_time:                         0
% 2.89/1.02  parsing_time:                           0.014
% 2.89/1.02  unif_index_cands_time:                  0.
% 2.89/1.02  unif_index_add_time:                    0.
% 2.89/1.02  orderings_time:                         0.
% 2.89/1.02  out_proof_time:                         0.016
% 2.89/1.02  total_time:                             0.247
% 2.89/1.02  num_of_symbols:                         50
% 2.89/1.02  num_of_terms:                           5082
% 2.89/1.02  
% 2.89/1.02  ------ Preprocessing
% 2.89/1.02  
% 2.89/1.02  num_of_splits:                          0
% 2.89/1.02  num_of_split_atoms:                     0
% 2.89/1.02  num_of_reused_defs:                     0
% 2.89/1.02  num_eq_ax_congr_red:                    17
% 2.89/1.02  num_of_sem_filtered_clauses:            1
% 2.89/1.02  num_of_subtypes:                        0
% 2.89/1.02  monotx_restored_types:                  0
% 2.89/1.02  sat_num_of_epr_types:                   0
% 2.89/1.02  sat_num_of_non_cyclic_types:            0
% 2.89/1.02  sat_guarded_non_collapsed_types:        0
% 2.89/1.02  num_pure_diseq_elim:                    0
% 2.89/1.02  simp_replaced_by:                       0
% 2.89/1.02  res_preprocessed:                       145
% 2.89/1.02  prep_upred:                             0
% 2.89/1.02  prep_unflattend:                        84
% 2.89/1.02  smt_new_axioms:                         0
% 2.89/1.02  pred_elim_cands:                        5
% 2.89/1.02  pred_elim:                              1
% 2.89/1.02  pred_elim_cl:                           4
% 2.89/1.02  pred_elim_cycles:                       7
% 2.89/1.02  merged_defs:                            8
% 2.89/1.02  merged_defs_ncl:                        0
% 2.89/1.02  bin_hyper_res:                          8
% 2.89/1.02  prep_cycles:                            4
% 2.89/1.02  pred_elim_time:                         0.016
% 2.89/1.02  splitting_time:                         0.
% 2.89/1.02  sem_filter_time:                        0.
% 2.89/1.02  monotx_time:                            0.
% 2.89/1.02  subtype_inf_time:                       0.
% 2.89/1.02  
% 2.89/1.02  ------ Problem properties
% 2.89/1.02  
% 2.89/1.02  clauses:                                28
% 2.89/1.02  conjectures:                            3
% 2.89/1.02  epr:                                    5
% 2.89/1.02  horn:                                   21
% 2.89/1.02  ground:                                 6
% 2.89/1.02  unary:                                  10
% 2.89/1.02  binary:                                 10
% 2.89/1.02  lits:                                   56
% 2.89/1.02  lits_eq:                                23
% 2.89/1.02  fd_pure:                                0
% 2.89/1.02  fd_pseudo:                              0
% 2.89/1.02  fd_cond:                                3
% 2.89/1.02  fd_pseudo_cond:                         0
% 2.89/1.02  ac_symbols:                             0
% 2.89/1.02  
% 2.89/1.02  ------ Propositional Solver
% 2.89/1.02  
% 2.89/1.02  prop_solver_calls:                      29
% 2.89/1.02  prop_fast_solver_calls:                 1124
% 2.89/1.02  smt_solver_calls:                       0
% 2.89/1.02  smt_fast_solver_calls:                  0
% 2.89/1.02  prop_num_of_clauses:                    2231
% 2.89/1.02  prop_preprocess_simplified:             6417
% 2.89/1.02  prop_fo_subsumed:                       20
% 2.89/1.02  prop_solver_time:                       0.
% 2.89/1.02  smt_solver_time:                        0.
% 2.89/1.02  smt_fast_solver_time:                   0.
% 2.89/1.02  prop_fast_solver_time:                  0.
% 2.89/1.02  prop_unsat_core_time:                   0.
% 2.89/1.02  
% 2.89/1.02  ------ QBF
% 2.89/1.02  
% 2.89/1.02  qbf_q_res:                              0
% 2.89/1.02  qbf_num_tautologies:                    0
% 2.89/1.02  qbf_prep_cycles:                        0
% 2.89/1.02  
% 2.89/1.02  ------ BMC1
% 2.89/1.02  
% 2.89/1.02  bmc1_current_bound:                     -1
% 2.89/1.02  bmc1_last_solved_bound:                 -1
% 2.89/1.02  bmc1_unsat_core_size:                   -1
% 2.89/1.02  bmc1_unsat_core_parents_size:           -1
% 2.89/1.02  bmc1_merge_next_fun:                    0
% 2.89/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.89/1.02  
% 2.89/1.02  ------ Instantiation
% 2.89/1.02  
% 2.89/1.02  inst_num_of_clauses:                    767
% 2.89/1.02  inst_num_in_passive:                    372
% 2.89/1.02  inst_num_in_active:                     391
% 2.89/1.02  inst_num_in_unprocessed:                4
% 2.89/1.02  inst_num_of_loops:                      530
% 2.89/1.02  inst_num_of_learning_restarts:          0
% 2.89/1.02  inst_num_moves_active_passive:          135
% 2.89/1.02  inst_lit_activity:                      0
% 2.89/1.02  inst_lit_activity_moves:                0
% 2.89/1.02  inst_num_tautologies:                   0
% 2.89/1.02  inst_num_prop_implied:                  0
% 2.89/1.02  inst_num_existing_simplified:           0
% 2.89/1.02  inst_num_eq_res_simplified:             0
% 2.89/1.02  inst_num_child_elim:                    0
% 2.89/1.02  inst_num_of_dismatching_blockings:      119
% 2.89/1.02  inst_num_of_non_proper_insts:           567
% 2.89/1.02  inst_num_of_duplicates:                 0
% 2.89/1.02  inst_inst_num_from_inst_to_res:         0
% 2.89/1.02  inst_dismatching_checking_time:         0.
% 2.89/1.02  
% 2.89/1.02  ------ Resolution
% 2.89/1.02  
% 2.89/1.02  res_num_of_clauses:                     0
% 2.89/1.02  res_num_in_passive:                     0
% 2.89/1.02  res_num_in_active:                      0
% 2.89/1.02  res_num_of_loops:                       149
% 2.89/1.02  res_forward_subset_subsumed:            32
% 2.89/1.02  res_backward_subset_subsumed:           0
% 2.89/1.02  res_forward_subsumed:                   0
% 2.89/1.02  res_backward_subsumed:                  0
% 2.89/1.02  res_forward_subsumption_resolution:     3
% 2.89/1.02  res_backward_subsumption_resolution:    0
% 2.89/1.02  res_clause_to_clause_subsumption:       379
% 2.89/1.02  res_orphan_elimination:                 0
% 2.89/1.02  res_tautology_del:                      91
% 2.89/1.02  res_num_eq_res_simplified:              0
% 2.89/1.02  res_num_sel_changes:                    0
% 2.89/1.02  res_moves_from_active_to_pass:          0
% 2.89/1.02  
% 2.89/1.02  ------ Superposition
% 2.89/1.02  
% 2.89/1.02  sup_time_total:                         0.
% 2.89/1.02  sup_time_generating:                    0.
% 2.89/1.02  sup_time_sim_full:                      0.
% 2.89/1.02  sup_time_sim_immed:                     0.
% 2.89/1.02  
% 2.89/1.02  sup_num_of_clauses:                     88
% 2.89/1.02  sup_num_in_active:                      52
% 2.89/1.02  sup_num_in_passive:                     36
% 2.89/1.02  sup_num_of_loops:                       104
% 2.89/1.02  sup_fw_superposition:                   110
% 2.89/1.02  sup_bw_superposition:                   183
% 2.89/1.02  sup_immediate_simplified:               109
% 2.89/1.02  sup_given_eliminated:                   1
% 2.89/1.02  comparisons_done:                       0
% 2.89/1.02  comparisons_avoided:                    63
% 2.89/1.02  
% 2.89/1.02  ------ Simplifications
% 2.89/1.02  
% 2.89/1.02  
% 2.89/1.02  sim_fw_subset_subsumed:                 76
% 2.89/1.02  sim_bw_subset_subsumed:                 31
% 2.89/1.02  sim_fw_subsumed:                        18
% 2.89/1.02  sim_bw_subsumed:                        4
% 2.89/1.02  sim_fw_subsumption_res:                 6
% 2.89/1.02  sim_bw_subsumption_res:                 0
% 2.89/1.02  sim_tautology_del:                      8
% 2.89/1.02  sim_eq_tautology_del:                   30
% 2.89/1.02  sim_eq_res_simp:                        0
% 2.89/1.02  sim_fw_demodulated:                     24
% 2.89/1.02  sim_bw_demodulated:                     39
% 2.89/1.02  sim_light_normalised:                   12
% 2.89/1.02  sim_joinable_taut:                      0
% 2.89/1.02  sim_joinable_simp:                      0
% 2.89/1.02  sim_ac_normalised:                      0
% 2.89/1.02  sim_smt_subsumption:                    0
% 2.89/1.02  
%------------------------------------------------------------------------------
