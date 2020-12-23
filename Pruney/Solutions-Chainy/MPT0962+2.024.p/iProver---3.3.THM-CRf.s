%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:13 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 838 expanded)
%              Number of clauses        :   87 ( 306 expanded)
%              Number of leaves         :   19 ( 161 expanded)
%              Depth                    :   25
%              Number of atoms          :  436 (3276 expanded)
%              Number of equality atoms :  195 ( 747 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_relat_1(sK1(X0,X1))
        & v1_xboole_0(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      & v1_xboole_0(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).

fof(f74,plain,(
    ! [X0,X1] : m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X0,X1] : v1_xboole_0(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
        | ~ v1_funct_1(sK3) )
      & r1_tarski(k2_relat_1(sK3),sK2)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) )
    & r1_tarski(k2_relat_1(sK3),sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f44])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_30,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1480,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( v1_xboole_0(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1481,plain,
    ( v1_xboole_0(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1493,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2156,plain,
    ( sK1(X0,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1481,c_1493])).

cnf(c_2205,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1480,c_2156])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1484,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3451,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2205,c_1484])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3463,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3451,c_14])).

cnf(c_3487,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3463])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_176,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_33])).

cnf(c_177,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK3) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_177])).

cnf(c_617,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_625,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_617,c_20])).

cnf(c_1474,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2365,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_1474])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1708,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1759,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_1821,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1822,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_966,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1728,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1851,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_965,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1852,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_2504,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2365,c_34,c_32,c_625,c_1821,c_1822,c_1851,c_1852])).

cnf(c_1479,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_243,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_244])).

cnf(c_404,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_303])).

cnf(c_405,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1477,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_2276,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1477])).

cnf(c_2508,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2504,c_2276])).

cnf(c_2160,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2156,c_1481])).

cnf(c_2637,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2508,c_2160])).

cnf(c_2642,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2637,c_1493])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1488,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2976,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_1488])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2986,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2976,c_6])).

cnf(c_35,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3000,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_35])).

cnf(c_3005,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3000,c_1477])).

cnf(c_1834,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1835,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_1837,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_3373,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_35,c_1837,c_2160,c_2986])).

cnf(c_3378,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3373,c_1493])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_177])).

cnf(c_601,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_1475,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1580,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1475,c_7])).

cnf(c_2510,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2504,c_1580])).

cnf(c_2519,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2510,c_6])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_526,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_527,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_2421,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_1493])).

cnf(c_2507,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2504,c_2421])).

cnf(c_2781,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2519,c_527,c_2160,c_2507])).

cnf(c_3417,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3378,c_2781])).

cnf(c_98,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_100,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_93,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_95,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3487,c_3417,c_100,c_95])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:10:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.77/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.03  
% 1.77/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.77/1.03  
% 1.77/1.03  ------  iProver source info
% 1.77/1.03  
% 1.77/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.77/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.77/1.03  git: non_committed_changes: false
% 1.77/1.03  git: last_make_outside_of_git: false
% 1.77/1.03  
% 1.77/1.03  ------ 
% 1.77/1.03  
% 1.77/1.03  ------ Input Options
% 1.77/1.03  
% 1.77/1.03  --out_options                           all
% 1.77/1.03  --tptp_safe_out                         true
% 1.77/1.03  --problem_path                          ""
% 1.77/1.03  --include_path                          ""
% 1.77/1.03  --clausifier                            res/vclausify_rel
% 1.77/1.03  --clausifier_options                    --mode clausify
% 1.77/1.03  --stdin                                 false
% 1.77/1.03  --stats_out                             all
% 1.77/1.03  
% 1.77/1.03  ------ General Options
% 1.77/1.03  
% 1.77/1.03  --fof                                   false
% 1.77/1.03  --time_out_real                         305.
% 1.77/1.03  --time_out_virtual                      -1.
% 1.77/1.03  --symbol_type_check                     false
% 1.77/1.03  --clausify_out                          false
% 1.77/1.03  --sig_cnt_out                           false
% 1.77/1.03  --trig_cnt_out                          false
% 1.77/1.03  --trig_cnt_out_tolerance                1.
% 1.77/1.03  --trig_cnt_out_sk_spl                   false
% 1.77/1.03  --abstr_cl_out                          false
% 1.77/1.03  
% 1.77/1.03  ------ Global Options
% 1.77/1.03  
% 1.77/1.03  --schedule                              default
% 1.77/1.03  --add_important_lit                     false
% 1.77/1.03  --prop_solver_per_cl                    1000
% 1.77/1.03  --min_unsat_core                        false
% 1.77/1.03  --soft_assumptions                      false
% 1.77/1.03  --soft_lemma_size                       3
% 1.77/1.03  --prop_impl_unit_size                   0
% 1.77/1.03  --prop_impl_unit                        []
% 1.77/1.03  --share_sel_clauses                     true
% 1.77/1.03  --reset_solvers                         false
% 1.77/1.03  --bc_imp_inh                            [conj_cone]
% 1.77/1.03  --conj_cone_tolerance                   3.
% 1.77/1.03  --extra_neg_conj                        none
% 1.77/1.03  --large_theory_mode                     true
% 1.77/1.03  --prolific_symb_bound                   200
% 1.77/1.03  --lt_threshold                          2000
% 1.77/1.03  --clause_weak_htbl                      true
% 1.77/1.03  --gc_record_bc_elim                     false
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing Options
% 1.77/1.03  
% 1.77/1.03  --preprocessing_flag                    true
% 1.77/1.03  --time_out_prep_mult                    0.1
% 1.77/1.03  --splitting_mode                        input
% 1.77/1.03  --splitting_grd                         true
% 1.77/1.03  --splitting_cvd                         false
% 1.77/1.03  --splitting_cvd_svl                     false
% 1.77/1.03  --splitting_nvd                         32
% 1.77/1.03  --sub_typing                            true
% 1.77/1.03  --prep_gs_sim                           true
% 1.77/1.03  --prep_unflatten                        true
% 1.77/1.03  --prep_res_sim                          true
% 1.77/1.03  --prep_upred                            true
% 1.77/1.03  --prep_sem_filter                       exhaustive
% 1.77/1.03  --prep_sem_filter_out                   false
% 1.77/1.03  --pred_elim                             true
% 1.77/1.03  --res_sim_input                         true
% 1.77/1.03  --eq_ax_congr_red                       true
% 1.77/1.03  --pure_diseq_elim                       true
% 1.77/1.03  --brand_transform                       false
% 1.77/1.03  --non_eq_to_eq                          false
% 1.77/1.03  --prep_def_merge                        true
% 1.77/1.03  --prep_def_merge_prop_impl              false
% 1.77/1.03  --prep_def_merge_mbd                    true
% 1.77/1.03  --prep_def_merge_tr_red                 false
% 1.77/1.03  --prep_def_merge_tr_cl                  false
% 1.77/1.03  --smt_preprocessing                     true
% 1.77/1.03  --smt_ac_axioms                         fast
% 1.77/1.03  --preprocessed_out                      false
% 1.77/1.03  --preprocessed_stats                    false
% 1.77/1.03  
% 1.77/1.03  ------ Abstraction refinement Options
% 1.77/1.03  
% 1.77/1.03  --abstr_ref                             []
% 1.77/1.03  --abstr_ref_prep                        false
% 1.77/1.03  --abstr_ref_until_sat                   false
% 1.77/1.03  --abstr_ref_sig_restrict                funpre
% 1.77/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.03  --abstr_ref_under                       []
% 1.77/1.03  
% 1.77/1.03  ------ SAT Options
% 1.77/1.03  
% 1.77/1.03  --sat_mode                              false
% 1.77/1.03  --sat_fm_restart_options                ""
% 1.77/1.03  --sat_gr_def                            false
% 1.77/1.03  --sat_epr_types                         true
% 1.77/1.03  --sat_non_cyclic_types                  false
% 1.77/1.03  --sat_finite_models                     false
% 1.77/1.03  --sat_fm_lemmas                         false
% 1.77/1.03  --sat_fm_prep                           false
% 1.77/1.03  --sat_fm_uc_incr                        true
% 1.77/1.03  --sat_out_model                         small
% 1.77/1.03  --sat_out_clauses                       false
% 1.77/1.03  
% 1.77/1.03  ------ QBF Options
% 1.77/1.03  
% 1.77/1.03  --qbf_mode                              false
% 1.77/1.03  --qbf_elim_univ                         false
% 1.77/1.03  --qbf_dom_inst                          none
% 1.77/1.03  --qbf_dom_pre_inst                      false
% 1.77/1.03  --qbf_sk_in                             false
% 1.77/1.03  --qbf_pred_elim                         true
% 1.77/1.03  --qbf_split                             512
% 1.77/1.03  
% 1.77/1.03  ------ BMC1 Options
% 1.77/1.03  
% 1.77/1.03  --bmc1_incremental                      false
% 1.77/1.03  --bmc1_axioms                           reachable_all
% 1.77/1.03  --bmc1_min_bound                        0
% 1.77/1.03  --bmc1_max_bound                        -1
% 1.77/1.03  --bmc1_max_bound_default                -1
% 1.77/1.03  --bmc1_symbol_reachability              true
% 1.77/1.03  --bmc1_property_lemmas                  false
% 1.77/1.03  --bmc1_k_induction                      false
% 1.77/1.03  --bmc1_non_equiv_states                 false
% 1.77/1.03  --bmc1_deadlock                         false
% 1.77/1.03  --bmc1_ucm                              false
% 1.77/1.03  --bmc1_add_unsat_core                   none
% 1.77/1.03  --bmc1_unsat_core_children              false
% 1.77/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.03  --bmc1_out_stat                         full
% 1.77/1.03  --bmc1_ground_init                      false
% 1.77/1.03  --bmc1_pre_inst_next_state              false
% 1.77/1.03  --bmc1_pre_inst_state                   false
% 1.77/1.03  --bmc1_pre_inst_reach_state             false
% 1.77/1.03  --bmc1_out_unsat_core                   false
% 1.77/1.03  --bmc1_aig_witness_out                  false
% 1.77/1.03  --bmc1_verbose                          false
% 1.77/1.03  --bmc1_dump_clauses_tptp                false
% 1.77/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.03  --bmc1_dump_file                        -
% 1.77/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.03  --bmc1_ucm_extend_mode                  1
% 1.77/1.03  --bmc1_ucm_init_mode                    2
% 1.77/1.03  --bmc1_ucm_cone_mode                    none
% 1.77/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.03  --bmc1_ucm_relax_model                  4
% 1.77/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.03  --bmc1_ucm_layered_model                none
% 1.77/1.03  --bmc1_ucm_max_lemma_size               10
% 1.77/1.03  
% 1.77/1.03  ------ AIG Options
% 1.77/1.03  
% 1.77/1.03  --aig_mode                              false
% 1.77/1.03  
% 1.77/1.03  ------ Instantiation Options
% 1.77/1.03  
% 1.77/1.03  --instantiation_flag                    true
% 1.77/1.03  --inst_sos_flag                         false
% 1.77/1.03  --inst_sos_phase                        true
% 1.77/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.03  --inst_lit_sel_side                     num_symb
% 1.77/1.03  --inst_solver_per_active                1400
% 1.77/1.03  --inst_solver_calls_frac                1.
% 1.77/1.03  --inst_passive_queue_type               priority_queues
% 1.77/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.03  --inst_passive_queues_freq              [25;2]
% 1.77/1.03  --inst_dismatching                      true
% 1.77/1.03  --inst_eager_unprocessed_to_passive     true
% 1.77/1.03  --inst_prop_sim_given                   true
% 1.77/1.03  --inst_prop_sim_new                     false
% 1.77/1.03  --inst_subs_new                         false
% 1.77/1.03  --inst_eq_res_simp                      false
% 1.77/1.03  --inst_subs_given                       false
% 1.77/1.03  --inst_orphan_elimination               true
% 1.77/1.03  --inst_learning_loop_flag               true
% 1.77/1.03  --inst_learning_start                   3000
% 1.77/1.03  --inst_learning_factor                  2
% 1.77/1.03  --inst_start_prop_sim_after_learn       3
% 1.77/1.03  --inst_sel_renew                        solver
% 1.77/1.03  --inst_lit_activity_flag                true
% 1.77/1.03  --inst_restr_to_given                   false
% 1.77/1.03  --inst_activity_threshold               500
% 1.77/1.03  --inst_out_proof                        true
% 1.77/1.03  
% 1.77/1.03  ------ Resolution Options
% 1.77/1.03  
% 1.77/1.03  --resolution_flag                       true
% 1.77/1.03  --res_lit_sel                           adaptive
% 1.77/1.03  --res_lit_sel_side                      none
% 1.77/1.03  --res_ordering                          kbo
% 1.77/1.03  --res_to_prop_solver                    active
% 1.77/1.03  --res_prop_simpl_new                    false
% 1.77/1.03  --res_prop_simpl_given                  true
% 1.77/1.03  --res_passive_queue_type                priority_queues
% 1.77/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.03  --res_passive_queues_freq               [15;5]
% 1.77/1.03  --res_forward_subs                      full
% 1.77/1.03  --res_backward_subs                     full
% 1.77/1.03  --res_forward_subs_resolution           true
% 1.77/1.03  --res_backward_subs_resolution          true
% 1.77/1.03  --res_orphan_elimination                true
% 1.77/1.03  --res_time_limit                        2.
% 1.77/1.03  --res_out_proof                         true
% 1.77/1.03  
% 1.77/1.03  ------ Superposition Options
% 1.77/1.03  
% 1.77/1.03  --superposition_flag                    true
% 1.77/1.03  --sup_passive_queue_type                priority_queues
% 1.77/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.03  --demod_completeness_check              fast
% 1.77/1.03  --demod_use_ground                      true
% 1.77/1.03  --sup_to_prop_solver                    passive
% 1.77/1.03  --sup_prop_simpl_new                    true
% 1.77/1.03  --sup_prop_simpl_given                  true
% 1.77/1.03  --sup_fun_splitting                     false
% 1.77/1.03  --sup_smt_interval                      50000
% 1.77/1.03  
% 1.77/1.03  ------ Superposition Simplification Setup
% 1.77/1.03  
% 1.77/1.03  --sup_indices_passive                   []
% 1.77/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_full_bw                           [BwDemod]
% 1.77/1.03  --sup_immed_triv                        [TrivRules]
% 1.77/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_immed_bw_main                     []
% 1.77/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.03  
% 1.77/1.03  ------ Combination Options
% 1.77/1.03  
% 1.77/1.03  --comb_res_mult                         3
% 1.77/1.03  --comb_sup_mult                         2
% 1.77/1.03  --comb_inst_mult                        10
% 1.77/1.03  
% 1.77/1.03  ------ Debug Options
% 1.77/1.03  
% 1.77/1.03  --dbg_backtrace                         false
% 1.77/1.03  --dbg_dump_prop_clauses                 false
% 1.77/1.03  --dbg_dump_prop_clauses_file            -
% 1.77/1.03  --dbg_out_stat                          false
% 1.77/1.03  ------ Parsing...
% 1.77/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.77/1.03  ------ Proving...
% 1.77/1.03  ------ Problem Properties 
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  clauses                                 26
% 1.77/1.03  conjectures                             2
% 1.77/1.03  EPR                                     5
% 1.77/1.03  Horn                                    25
% 1.77/1.03  unary                                   12
% 1.77/1.03  binary                                  6
% 1.77/1.03  lits                                    52
% 1.77/1.03  lits eq                                 21
% 1.77/1.03  fd_pure                                 0
% 1.77/1.03  fd_pseudo                               0
% 1.77/1.03  fd_cond                                 2
% 1.77/1.03  fd_pseudo_cond                          1
% 1.77/1.03  AC symbols                              0
% 1.77/1.03  
% 1.77/1.03  ------ Schedule dynamic 5 is on 
% 1.77/1.03  
% 1.77/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  ------ 
% 1.77/1.03  Current options:
% 1.77/1.03  ------ 
% 1.77/1.03  
% 1.77/1.03  ------ Input Options
% 1.77/1.03  
% 1.77/1.03  --out_options                           all
% 1.77/1.03  --tptp_safe_out                         true
% 1.77/1.03  --problem_path                          ""
% 1.77/1.03  --include_path                          ""
% 1.77/1.03  --clausifier                            res/vclausify_rel
% 1.77/1.03  --clausifier_options                    --mode clausify
% 1.77/1.03  --stdin                                 false
% 1.77/1.03  --stats_out                             all
% 1.77/1.03  
% 1.77/1.03  ------ General Options
% 1.77/1.03  
% 1.77/1.03  --fof                                   false
% 1.77/1.03  --time_out_real                         305.
% 1.77/1.03  --time_out_virtual                      -1.
% 1.77/1.03  --symbol_type_check                     false
% 1.77/1.03  --clausify_out                          false
% 1.77/1.03  --sig_cnt_out                           false
% 1.77/1.03  --trig_cnt_out                          false
% 1.77/1.03  --trig_cnt_out_tolerance                1.
% 1.77/1.03  --trig_cnt_out_sk_spl                   false
% 1.77/1.03  --abstr_cl_out                          false
% 1.77/1.03  
% 1.77/1.03  ------ Global Options
% 1.77/1.03  
% 1.77/1.03  --schedule                              default
% 1.77/1.03  --add_important_lit                     false
% 1.77/1.03  --prop_solver_per_cl                    1000
% 1.77/1.03  --min_unsat_core                        false
% 1.77/1.03  --soft_assumptions                      false
% 1.77/1.03  --soft_lemma_size                       3
% 1.77/1.03  --prop_impl_unit_size                   0
% 1.77/1.03  --prop_impl_unit                        []
% 1.77/1.03  --share_sel_clauses                     true
% 1.77/1.03  --reset_solvers                         false
% 1.77/1.03  --bc_imp_inh                            [conj_cone]
% 1.77/1.03  --conj_cone_tolerance                   3.
% 1.77/1.03  --extra_neg_conj                        none
% 1.77/1.03  --large_theory_mode                     true
% 1.77/1.03  --prolific_symb_bound                   200
% 1.77/1.03  --lt_threshold                          2000
% 1.77/1.03  --clause_weak_htbl                      true
% 1.77/1.03  --gc_record_bc_elim                     false
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing Options
% 1.77/1.03  
% 1.77/1.03  --preprocessing_flag                    true
% 1.77/1.03  --time_out_prep_mult                    0.1
% 1.77/1.03  --splitting_mode                        input
% 1.77/1.03  --splitting_grd                         true
% 1.77/1.03  --splitting_cvd                         false
% 1.77/1.03  --splitting_cvd_svl                     false
% 1.77/1.03  --splitting_nvd                         32
% 1.77/1.03  --sub_typing                            true
% 1.77/1.03  --prep_gs_sim                           true
% 1.77/1.03  --prep_unflatten                        true
% 1.77/1.03  --prep_res_sim                          true
% 1.77/1.03  --prep_upred                            true
% 1.77/1.03  --prep_sem_filter                       exhaustive
% 1.77/1.03  --prep_sem_filter_out                   false
% 1.77/1.03  --pred_elim                             true
% 1.77/1.03  --res_sim_input                         true
% 1.77/1.03  --eq_ax_congr_red                       true
% 1.77/1.03  --pure_diseq_elim                       true
% 1.77/1.03  --brand_transform                       false
% 1.77/1.03  --non_eq_to_eq                          false
% 1.77/1.03  --prep_def_merge                        true
% 1.77/1.03  --prep_def_merge_prop_impl              false
% 1.77/1.03  --prep_def_merge_mbd                    true
% 1.77/1.03  --prep_def_merge_tr_red                 false
% 1.77/1.03  --prep_def_merge_tr_cl                  false
% 1.77/1.03  --smt_preprocessing                     true
% 1.77/1.03  --smt_ac_axioms                         fast
% 1.77/1.03  --preprocessed_out                      false
% 1.77/1.03  --preprocessed_stats                    false
% 1.77/1.03  
% 1.77/1.03  ------ Abstraction refinement Options
% 1.77/1.03  
% 1.77/1.03  --abstr_ref                             []
% 1.77/1.03  --abstr_ref_prep                        false
% 1.77/1.03  --abstr_ref_until_sat                   false
% 1.77/1.03  --abstr_ref_sig_restrict                funpre
% 1.77/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.03  --abstr_ref_under                       []
% 1.77/1.03  
% 1.77/1.03  ------ SAT Options
% 1.77/1.03  
% 1.77/1.03  --sat_mode                              false
% 1.77/1.03  --sat_fm_restart_options                ""
% 1.77/1.03  --sat_gr_def                            false
% 1.77/1.03  --sat_epr_types                         true
% 1.77/1.03  --sat_non_cyclic_types                  false
% 1.77/1.03  --sat_finite_models                     false
% 1.77/1.03  --sat_fm_lemmas                         false
% 1.77/1.03  --sat_fm_prep                           false
% 1.77/1.03  --sat_fm_uc_incr                        true
% 1.77/1.03  --sat_out_model                         small
% 1.77/1.03  --sat_out_clauses                       false
% 1.77/1.03  
% 1.77/1.03  ------ QBF Options
% 1.77/1.03  
% 1.77/1.03  --qbf_mode                              false
% 1.77/1.03  --qbf_elim_univ                         false
% 1.77/1.03  --qbf_dom_inst                          none
% 1.77/1.03  --qbf_dom_pre_inst                      false
% 1.77/1.03  --qbf_sk_in                             false
% 1.77/1.03  --qbf_pred_elim                         true
% 1.77/1.03  --qbf_split                             512
% 1.77/1.03  
% 1.77/1.03  ------ BMC1 Options
% 1.77/1.03  
% 1.77/1.03  --bmc1_incremental                      false
% 1.77/1.03  --bmc1_axioms                           reachable_all
% 1.77/1.03  --bmc1_min_bound                        0
% 1.77/1.03  --bmc1_max_bound                        -1
% 1.77/1.03  --bmc1_max_bound_default                -1
% 1.77/1.03  --bmc1_symbol_reachability              true
% 1.77/1.03  --bmc1_property_lemmas                  false
% 1.77/1.03  --bmc1_k_induction                      false
% 1.77/1.03  --bmc1_non_equiv_states                 false
% 1.77/1.03  --bmc1_deadlock                         false
% 1.77/1.03  --bmc1_ucm                              false
% 1.77/1.03  --bmc1_add_unsat_core                   none
% 1.77/1.03  --bmc1_unsat_core_children              false
% 1.77/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.03  --bmc1_out_stat                         full
% 1.77/1.03  --bmc1_ground_init                      false
% 1.77/1.03  --bmc1_pre_inst_next_state              false
% 1.77/1.03  --bmc1_pre_inst_state                   false
% 1.77/1.03  --bmc1_pre_inst_reach_state             false
% 1.77/1.03  --bmc1_out_unsat_core                   false
% 1.77/1.03  --bmc1_aig_witness_out                  false
% 1.77/1.03  --bmc1_verbose                          false
% 1.77/1.03  --bmc1_dump_clauses_tptp                false
% 1.77/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.03  --bmc1_dump_file                        -
% 1.77/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.03  --bmc1_ucm_extend_mode                  1
% 1.77/1.03  --bmc1_ucm_init_mode                    2
% 1.77/1.03  --bmc1_ucm_cone_mode                    none
% 1.77/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.03  --bmc1_ucm_relax_model                  4
% 1.77/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.03  --bmc1_ucm_layered_model                none
% 1.77/1.03  --bmc1_ucm_max_lemma_size               10
% 1.77/1.03  
% 1.77/1.03  ------ AIG Options
% 1.77/1.03  
% 1.77/1.03  --aig_mode                              false
% 1.77/1.03  
% 1.77/1.03  ------ Instantiation Options
% 1.77/1.03  
% 1.77/1.03  --instantiation_flag                    true
% 1.77/1.03  --inst_sos_flag                         false
% 1.77/1.03  --inst_sos_phase                        true
% 1.77/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.03  --inst_lit_sel_side                     none
% 1.77/1.03  --inst_solver_per_active                1400
% 1.77/1.03  --inst_solver_calls_frac                1.
% 1.77/1.03  --inst_passive_queue_type               priority_queues
% 1.77/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.03  --inst_passive_queues_freq              [25;2]
% 1.77/1.03  --inst_dismatching                      true
% 1.77/1.03  --inst_eager_unprocessed_to_passive     true
% 1.77/1.03  --inst_prop_sim_given                   true
% 1.77/1.03  --inst_prop_sim_new                     false
% 1.77/1.03  --inst_subs_new                         false
% 1.77/1.03  --inst_eq_res_simp                      false
% 1.77/1.03  --inst_subs_given                       false
% 1.77/1.03  --inst_orphan_elimination               true
% 1.77/1.03  --inst_learning_loop_flag               true
% 1.77/1.03  --inst_learning_start                   3000
% 1.77/1.03  --inst_learning_factor                  2
% 1.77/1.03  --inst_start_prop_sim_after_learn       3
% 1.77/1.03  --inst_sel_renew                        solver
% 1.77/1.03  --inst_lit_activity_flag                true
% 1.77/1.03  --inst_restr_to_given                   false
% 1.77/1.03  --inst_activity_threshold               500
% 1.77/1.03  --inst_out_proof                        true
% 1.77/1.03  
% 1.77/1.03  ------ Resolution Options
% 1.77/1.03  
% 1.77/1.03  --resolution_flag                       false
% 1.77/1.03  --res_lit_sel                           adaptive
% 1.77/1.03  --res_lit_sel_side                      none
% 1.77/1.03  --res_ordering                          kbo
% 1.77/1.03  --res_to_prop_solver                    active
% 1.77/1.03  --res_prop_simpl_new                    false
% 1.77/1.03  --res_prop_simpl_given                  true
% 1.77/1.03  --res_passive_queue_type                priority_queues
% 1.77/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.03  --res_passive_queues_freq               [15;5]
% 1.77/1.03  --res_forward_subs                      full
% 1.77/1.03  --res_backward_subs                     full
% 1.77/1.03  --res_forward_subs_resolution           true
% 1.77/1.03  --res_backward_subs_resolution          true
% 1.77/1.03  --res_orphan_elimination                true
% 1.77/1.03  --res_time_limit                        2.
% 1.77/1.03  --res_out_proof                         true
% 1.77/1.03  
% 1.77/1.03  ------ Superposition Options
% 1.77/1.03  
% 1.77/1.03  --superposition_flag                    true
% 1.77/1.03  --sup_passive_queue_type                priority_queues
% 1.77/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.03  --demod_completeness_check              fast
% 1.77/1.03  --demod_use_ground                      true
% 1.77/1.03  --sup_to_prop_solver                    passive
% 1.77/1.03  --sup_prop_simpl_new                    true
% 1.77/1.03  --sup_prop_simpl_given                  true
% 1.77/1.03  --sup_fun_splitting                     false
% 1.77/1.03  --sup_smt_interval                      50000
% 1.77/1.03  
% 1.77/1.03  ------ Superposition Simplification Setup
% 1.77/1.03  
% 1.77/1.03  --sup_indices_passive                   []
% 1.77/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_full_bw                           [BwDemod]
% 1.77/1.03  --sup_immed_triv                        [TrivRules]
% 1.77/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_immed_bw_main                     []
% 1.77/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.03  
% 1.77/1.03  ------ Combination Options
% 1.77/1.03  
% 1.77/1.03  --comb_res_mult                         3
% 1.77/1.03  --comb_sup_mult                         2
% 1.77/1.03  --comb_inst_mult                        10
% 1.77/1.03  
% 1.77/1.03  ------ Debug Options
% 1.77/1.03  
% 1.77/1.03  --dbg_backtrace                         false
% 1.77/1.03  --dbg_dump_prop_clauses                 false
% 1.77/1.03  --dbg_dump_prop_clauses_file            -
% 1.77/1.03  --dbg_out_stat                          false
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  ------ Proving...
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  % SZS status Theorem for theBenchmark.p
% 1.77/1.03  
% 1.77/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.77/1.03  
% 1.77/1.03  fof(f15,axiom,(
% 1.77/1.03    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f18,plain,(
% 1.77/1.03    ! [X0,X1] : ? [X2] : (v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(pure_predicate_removal,[],[f15])).
% 1.77/1.03  
% 1.77/1.03  fof(f19,plain,(
% 1.77/1.03    ! [X0,X1] : ? [X2] : (v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(pure_predicate_removal,[],[f18])).
% 1.77/1.03  
% 1.77/1.03  fof(f42,plain,(
% 1.77/1.03    ! [X1,X0] : (? [X2] : (v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_relat_1(sK1(X0,X1)) & v1_xboole_0(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.77/1.03    introduced(choice_axiom,[])).
% 1.77/1.03  
% 1.77/1.03  fof(f43,plain,(
% 1.77/1.03    ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) & v1_xboole_0(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f42])).
% 1.77/1.03  
% 1.77/1.03  fof(f74,plain,(
% 1.77/1.03    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/1.03    inference(cnf_transformation,[],[f43])).
% 1.77/1.03  
% 1.77/1.03  fof(f75,plain,(
% 1.77/1.03    ( ! [X0,X1] : (v1_xboole_0(sK1(X0,X1))) )),
% 1.77/1.03    inference(cnf_transformation,[],[f43])).
% 1.77/1.03  
% 1.77/1.03  fof(f2,axiom,(
% 1.77/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f20,plain,(
% 1.77/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.77/1.03    inference(ennf_transformation,[],[f2])).
% 1.77/1.03  
% 1.77/1.03  fof(f48,plain,(
% 1.77/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f20])).
% 1.77/1.03  
% 1.77/1.03  fof(f12,axiom,(
% 1.77/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f24,plain,(
% 1.77/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(ennf_transformation,[],[f12])).
% 1.77/1.03  
% 1.77/1.03  fof(f66,plain,(
% 1.77/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/1.03    inference(cnf_transformation,[],[f24])).
% 1.77/1.03  
% 1.77/1.03  fof(f8,axiom,(
% 1.77/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f59,plain,(
% 1.77/1.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.77/1.03    inference(cnf_transformation,[],[f8])).
% 1.77/1.03  
% 1.77/1.03  fof(f5,axiom,(
% 1.77/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f39,plain,(
% 1.77/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.77/1.03    inference(nnf_transformation,[],[f5])).
% 1.77/1.03  
% 1.77/1.03  fof(f56,plain,(
% 1.77/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f39])).
% 1.77/1.03  
% 1.77/1.03  fof(f14,axiom,(
% 1.77/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f27,plain,(
% 1.77/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(ennf_transformation,[],[f14])).
% 1.77/1.03  
% 1.77/1.03  fof(f28,plain,(
% 1.77/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(flattening,[],[f27])).
% 1.77/1.03  
% 1.77/1.03  fof(f41,plain,(
% 1.77/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/1.03    inference(nnf_transformation,[],[f28])).
% 1.77/1.03  
% 1.77/1.03  fof(f70,plain,(
% 1.77/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/1.03    inference(cnf_transformation,[],[f41])).
% 1.77/1.03  
% 1.77/1.03  fof(f16,conjecture,(
% 1.77/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f17,negated_conjecture,(
% 1.77/1.03    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.77/1.03    inference(negated_conjecture,[],[f16])).
% 1.77/1.03  
% 1.77/1.03  fof(f29,plain,(
% 1.77/1.03    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.77/1.03    inference(ennf_transformation,[],[f17])).
% 1.77/1.03  
% 1.77/1.03  fof(f30,plain,(
% 1.77/1.03    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.77/1.03    inference(flattening,[],[f29])).
% 1.77/1.03  
% 1.77/1.03  fof(f44,plain,(
% 1.77/1.03    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.77/1.03    introduced(choice_axiom,[])).
% 1.77/1.03  
% 1.77/1.03  fof(f45,plain,(
% 1.77/1.03    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 1.77/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f44])).
% 1.77/1.03  
% 1.77/1.03  fof(f80,plain,(
% 1.77/1.03    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)),
% 1.77/1.03    inference(cnf_transformation,[],[f45])).
% 1.77/1.03  
% 1.77/1.03  fof(f78,plain,(
% 1.77/1.03    v1_funct_1(sK3)),
% 1.77/1.03    inference(cnf_transformation,[],[f45])).
% 1.77/1.03  
% 1.77/1.03  fof(f77,plain,(
% 1.77/1.03    v1_relat_1(sK3)),
% 1.77/1.03    inference(cnf_transformation,[],[f45])).
% 1.77/1.03  
% 1.77/1.03  fof(f79,plain,(
% 1.77/1.03    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.77/1.03    inference(cnf_transformation,[],[f45])).
% 1.77/1.03  
% 1.77/1.03  fof(f13,axiom,(
% 1.77/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f25,plain,(
% 1.77/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.77/1.03    inference(ennf_transformation,[],[f13])).
% 1.77/1.03  
% 1.77/1.03  fof(f26,plain,(
% 1.77/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.77/1.03    inference(flattening,[],[f25])).
% 1.77/1.03  
% 1.77/1.03  fof(f67,plain,(
% 1.77/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f26])).
% 1.77/1.03  
% 1.77/1.03  fof(f3,axiom,(
% 1.77/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f35,plain,(
% 1.77/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/1.03    inference(nnf_transformation,[],[f3])).
% 1.77/1.03  
% 1.77/1.03  fof(f36,plain,(
% 1.77/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/1.03    inference(flattening,[],[f35])).
% 1.77/1.03  
% 1.77/1.03  fof(f49,plain,(
% 1.77/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.77/1.03    inference(cnf_transformation,[],[f36])).
% 1.77/1.03  
% 1.77/1.03  fof(f82,plain,(
% 1.77/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.77/1.03    inference(equality_resolution,[],[f49])).
% 1.77/1.03  
% 1.77/1.03  fof(f1,axiom,(
% 1.77/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f31,plain,(
% 1.77/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.77/1.03    inference(nnf_transformation,[],[f1])).
% 1.77/1.03  
% 1.77/1.03  fof(f32,plain,(
% 1.77/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.77/1.03    inference(rectify,[],[f31])).
% 1.77/1.03  
% 1.77/1.03  fof(f33,plain,(
% 1.77/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.77/1.03    introduced(choice_axiom,[])).
% 1.77/1.03  
% 1.77/1.03  fof(f34,plain,(
% 1.77/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.77/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.77/1.03  
% 1.77/1.03  fof(f47,plain,(
% 1.77/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f34])).
% 1.77/1.03  
% 1.77/1.03  fof(f6,axiom,(
% 1.77/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f21,plain,(
% 1.77/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.77/1.03    inference(ennf_transformation,[],[f6])).
% 1.77/1.03  
% 1.77/1.03  fof(f57,plain,(
% 1.77/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f21])).
% 1.77/1.03  
% 1.77/1.03  fof(f7,axiom,(
% 1.77/1.03    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f22,plain,(
% 1.77/1.03    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.77/1.03    inference(ennf_transformation,[],[f7])).
% 1.77/1.03  
% 1.77/1.03  fof(f58,plain,(
% 1.77/1.03    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f22])).
% 1.77/1.03  
% 1.77/1.03  fof(f4,axiom,(
% 1.77/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f37,plain,(
% 1.77/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.77/1.03    inference(nnf_transformation,[],[f4])).
% 1.77/1.03  
% 1.77/1.03  fof(f38,plain,(
% 1.77/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.77/1.03    inference(flattening,[],[f37])).
% 1.77/1.03  
% 1.77/1.03  fof(f54,plain,(
% 1.77/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.77/1.03    inference(cnf_transformation,[],[f38])).
% 1.77/1.03  
% 1.77/1.03  fof(f83,plain,(
% 1.77/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.77/1.03    inference(equality_resolution,[],[f54])).
% 1.77/1.03  
% 1.77/1.03  fof(f71,plain,(
% 1.77/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/1.03    inference(cnf_transformation,[],[f41])).
% 1.77/1.03  
% 1.77/1.03  fof(f88,plain,(
% 1.77/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.77/1.03    inference(equality_resolution,[],[f71])).
% 1.77/1.03  
% 1.77/1.03  fof(f53,plain,(
% 1.77/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.77/1.03    inference(cnf_transformation,[],[f38])).
% 1.77/1.03  
% 1.77/1.03  fof(f84,plain,(
% 1.77/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/1.03    inference(equality_resolution,[],[f53])).
% 1.77/1.03  
% 1.77/1.03  fof(f9,axiom,(
% 1.77/1.03    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.77/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.03  
% 1.77/1.03  fof(f23,plain,(
% 1.77/1.03    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.77/1.03    inference(ennf_transformation,[],[f9])).
% 1.77/1.03  
% 1.77/1.03  fof(f40,plain,(
% 1.77/1.03    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.77/1.03    inference(nnf_transformation,[],[f23])).
% 1.77/1.03  
% 1.77/1.03  fof(f62,plain,(
% 1.77/1.03    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/1.03    inference(cnf_transformation,[],[f40])).
% 1.77/1.03  
% 1.77/1.03  cnf(c_30,plain,
% 1.77/1.03      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.77/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1480,plain,
% 1.77/1.03      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_29,plain,
% 1.77/1.03      ( v1_xboole_0(sK1(X0,X1)) ),
% 1.77/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1481,plain,
% 1.77/1.03      ( v1_xboole_0(sK1(X0,X1)) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2,plain,
% 1.77/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1493,plain,
% 1.77/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2156,plain,
% 1.77/1.03      ( sK1(X0,X1) = k1_xboole_0 ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_1481,c_1493]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2205,plain,
% 1.77/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 1.77/1.03      inference(light_normalisation,[status(thm)],[c_1480,c_2156]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_20,plain,
% 1.77/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.77/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1484,plain,
% 1.77/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.77/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3451,plain,
% 1.77/1.03      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_2205,c_1484]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_14,plain,
% 1.77/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3463,plain,
% 1.77/1.03      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 1.77/1.03      inference(light_normalisation,[status(thm)],[c_3451,c_14]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3487,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_3463]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_9,plain,
% 1.77/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.77/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1490,plain,
% 1.77/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.77/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_25,plain,
% 1.77/1.03      ( v1_funct_2(X0,X1,X2)
% 1.77/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.03      | k1_relset_1(X1,X2,X0) != X1
% 1.77/1.03      | k1_xboole_0 = X2 ),
% 1.77/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_31,negated_conjecture,
% 1.77/1.03      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 1.77/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | ~ v1_funct_1(sK3) ),
% 1.77/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_33,negated_conjecture,
% 1.77/1.03      ( v1_funct_1(sK3) ),
% 1.77/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_176,plain,
% 1.77/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_31,c_33]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_177,negated_conjecture,
% 1.77/1.03      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 1.77/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
% 1.77/1.03      inference(renaming,[status(thm)],[c_176]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_616,plain,
% 1.77/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | k1_relset_1(X1,X2,X0) != X1
% 1.77/1.03      | k1_relat_1(sK3) != X1
% 1.77/1.03      | sK2 != X2
% 1.77/1.03      | sK3 != X0
% 1.77/1.03      | k1_xboole_0 = X2 ),
% 1.77/1.03      inference(resolution_lifted,[status(thm)],[c_25,c_177]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_617,plain,
% 1.77/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
% 1.77/1.03      | k1_xboole_0 = sK2 ),
% 1.77/1.03      inference(unflattening,[status(thm)],[c_616]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_625,plain,
% 1.77/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | k1_xboole_0 = sK2 ),
% 1.77/1.03      inference(forward_subsumption_resolution,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_617,c_20]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1474,plain,
% 1.77/1.03      ( k1_xboole_0 = sK2
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2365,plain,
% 1.77/1.03      ( sK2 = k1_xboole_0
% 1.77/1.03      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_1490,c_1474]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_34,negated_conjecture,
% 1.77/1.03      ( v1_relat_1(sK3) ),
% 1.77/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_32,negated_conjecture,
% 1.77/1.03      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 1.77/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_21,plain,
% 1.77/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.03      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.77/1.03      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.77/1.03      | ~ v1_relat_1(X0) ),
% 1.77/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1708,plain,
% 1.77/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.77/1.03      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 1.77/1.03      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 1.77/1.03      | ~ v1_relat_1(sK3) ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1759,plain,
% 1.77/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 1.77/1.03      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 1.77/1.03      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 1.77/1.03      | ~ v1_relat_1(sK3) ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_1708]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1821,plain,
% 1.77/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 1.77/1.03      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 1.77/1.03      | ~ v1_relat_1(sK3) ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_1759]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_5,plain,
% 1.77/1.03      ( r1_tarski(X0,X0) ),
% 1.77/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1822,plain,
% 1.77/1.03      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_966,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1728,plain,
% 1.77/1.03      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_966]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1851,plain,
% 1.77/1.03      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_1728]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_965,plain,( X0 = X0 ),theory(equality) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1852,plain,
% 1.77/1.03      ( sK2 = sK2 ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_965]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2504,plain,
% 1.77/1.03      ( sK2 = k1_xboole_0 ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_2365,c_34,c_32,c_625,c_1821,c_1822,c_1851,c_1852]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1479,plain,
% 1.77/1.03      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_0,plain,
% 1.77/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.77/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_11,plain,
% 1.77/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.77/1.03      | ~ r2_hidden(X2,X0)
% 1.77/1.03      | ~ v1_xboole_0(X1) ),
% 1.77/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_243,plain,
% 1.77/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.77/1.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_244,plain,
% 1.77/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.77/1.03      inference(renaming,[status(thm)],[c_243]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_303,plain,
% 1.77/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 1.77/1.03      inference(bin_hyper_res,[status(thm)],[c_11,c_244]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_404,plain,
% 1.77/1.03      ( ~ r1_tarski(X0,X1)
% 1.77/1.03      | ~ v1_xboole_0(X1)
% 1.77/1.03      | v1_xboole_0(X2)
% 1.77/1.03      | X0 != X2
% 1.77/1.03      | sK0(X2) != X3 ),
% 1.77/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_303]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_405,plain,
% 1.77/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.77/1.03      inference(unflattening,[status(thm)],[c_404]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1477,plain,
% 1.77/1.03      ( r1_tarski(X0,X1) != iProver_top
% 1.77/1.03      | v1_xboole_0(X1) != iProver_top
% 1.77/1.03      | v1_xboole_0(X0) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2276,plain,
% 1.77/1.03      ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top
% 1.77/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_1479,c_1477]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2508,plain,
% 1.77/1.03      ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top
% 1.77/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2504,c_2276]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2160,plain,
% 1.77/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2156,c_1481]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2637,plain,
% 1.77/1.03      ( v1_xboole_0(k2_relat_1(sK3)) = iProver_top ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_2508,c_2160]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2642,plain,
% 1.77/1.03      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_2637,c_1493]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_12,plain,
% 1.77/1.03      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.77/1.03      | ~ v1_relat_1(X0) ),
% 1.77/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1488,plain,
% 1.77/1.03      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.77/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2976,plain,
% 1.77/1.03      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top
% 1.77/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_2642,c_1488]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_6,plain,
% 1.77/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2986,plain,
% 1.77/1.03      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 1.77/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2976,c_6]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_35,plain,
% 1.77/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3000,plain,
% 1.77/1.03      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_2986,c_35]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3005,plain,
% 1.77/1.03      ( v1_xboole_0(sK3) = iProver_top
% 1.77/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_3000,c_1477]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1834,plain,
% 1.77/1.03      ( ~ r1_tarski(sK3,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK3) ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_405]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1835,plain,
% 1.77/1.03      ( r1_tarski(sK3,X0) != iProver_top
% 1.77/1.03      | v1_xboole_0(X0) != iProver_top
% 1.77/1.03      | v1_xboole_0(sK3) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_1834]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1837,plain,
% 1.77/1.03      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 1.77/1.03      | v1_xboole_0(sK3) = iProver_top
% 1.77/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_1835]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3373,plain,
% 1.77/1.03      ( v1_xboole_0(sK3) = iProver_top ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_3005,c_35,c_1837,c_2160,c_2986]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3378,plain,
% 1.77/1.03      ( sK3 = k1_xboole_0 ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_3373,c_1493]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_24,plain,
% 1.77/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.77/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.77/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_600,plain,
% 1.77/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.77/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.77/1.03      | sK2 != X1
% 1.77/1.03      | sK3 != X0 ),
% 1.77/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_177]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_601,plain,
% 1.77/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 1.77/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 1.77/1.03      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.77/1.03      inference(unflattening,[status(thm)],[c_600]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1475,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_7,plain,
% 1.77/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_1580,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_1475,c_7]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2510,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2504,c_1580]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2519,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2510,c_6]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_15,plain,
% 1.77/1.03      ( ~ v1_relat_1(X0)
% 1.77/1.03      | k2_relat_1(X0) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(X0) = k1_xboole_0 ),
% 1.77/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_526,plain,
% 1.77/1.03      ( k2_relat_1(X0) != k1_xboole_0
% 1.77/1.03      | k1_relat_1(X0) = k1_xboole_0
% 1.77/1.03      | sK3 != X0 ),
% 1.77/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_527,plain,
% 1.77/1.03      ( k2_relat_1(sK3) != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.77/1.03      inference(unflattening,[status(thm)],[c_526]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2421,plain,
% 1.77/1.03      ( k2_relat_1(sK3) = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 1.77/1.03      inference(superposition,[status(thm)],[c_2276,c_1493]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2507,plain,
% 1.77/1.03      ( k2_relat_1(sK3) = k1_xboole_0
% 1.77/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_2504,c_2421]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_2781,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.77/1.03      inference(global_propositional_subsumption,
% 1.77/1.03                [status(thm)],
% 1.77/1.03                [c_2519,c_527,c_2160,c_2507]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_3417,plain,
% 1.77/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.77/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.77/1.03      inference(demodulation,[status(thm)],[c_3378,c_2781]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_98,plain,
% 1.77/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_100,plain,
% 1.77/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_98]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_93,plain,
% 1.77/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.77/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 1.77/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(c_95,plain,
% 1.77/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.77/1.03      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.77/1.03      inference(instantiation,[status(thm)],[c_93]) ).
% 1.77/1.03  
% 1.77/1.03  cnf(contradiction,plain,
% 1.77/1.03      ( $false ),
% 1.77/1.03      inference(minisat,[status(thm)],[c_3487,c_3417,c_100,c_95]) ).
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.77/1.03  
% 1.77/1.03  ------                               Statistics
% 1.77/1.03  
% 1.77/1.03  ------ General
% 1.77/1.03  
% 1.77/1.03  abstr_ref_over_cycles:                  0
% 1.77/1.03  abstr_ref_under_cycles:                 0
% 1.77/1.03  gc_basic_clause_elim:                   0
% 1.77/1.03  forced_gc_time:                         0
% 1.77/1.03  parsing_time:                           0.013
% 1.77/1.03  unif_index_cands_time:                  0.
% 1.77/1.03  unif_index_add_time:                    0.
% 1.77/1.03  orderings_time:                         0.
% 1.77/1.03  out_proof_time:                         0.012
% 1.77/1.03  total_time:                             0.181
% 1.77/1.03  num_of_symbols:                         49
% 1.77/1.03  num_of_terms:                           2992
% 1.77/1.03  
% 1.77/1.03  ------ Preprocessing
% 1.77/1.03  
% 1.77/1.03  num_of_splits:                          0
% 1.77/1.03  num_of_split_atoms:                     0
% 1.77/1.03  num_of_reused_defs:                     0
% 1.77/1.03  num_eq_ax_congr_red:                    10
% 1.77/1.03  num_of_sem_filtered_clauses:            3
% 1.77/1.03  num_of_subtypes:                        0
% 1.77/1.03  monotx_restored_types:                  0
% 1.77/1.03  sat_num_of_epr_types:                   0
% 1.77/1.03  sat_num_of_non_cyclic_types:            0
% 1.77/1.03  sat_guarded_non_collapsed_types:        0
% 1.77/1.03  num_pure_diseq_elim:                    0
% 1.77/1.03  simp_replaced_by:                       0
% 1.77/1.03  res_preprocessed:                       137
% 1.77/1.03  prep_upred:                             0
% 1.77/1.03  prep_unflattend:                        54
% 1.77/1.03  smt_new_axioms:                         0
% 1.77/1.03  pred_elim_cands:                        4
% 1.77/1.03  pred_elim:                              2
% 1.77/1.03  pred_elim_cl:                           6
% 1.77/1.03  pred_elim_cycles:                       5
% 1.77/1.03  merged_defs:                            8
% 1.77/1.03  merged_defs_ncl:                        0
% 1.77/1.03  bin_hyper_res:                          9
% 1.77/1.03  prep_cycles:                            4
% 1.77/1.03  pred_elim_time:                         0.01
% 1.77/1.03  splitting_time:                         0.
% 1.77/1.03  sem_filter_time:                        0.
% 1.77/1.03  monotx_time:                            0.
% 1.77/1.03  subtype_inf_time:                       0.
% 1.77/1.03  
% 1.77/1.03  ------ Problem properties
% 1.77/1.03  
% 1.77/1.03  clauses:                                26
% 1.77/1.03  conjectures:                            2
% 1.77/1.03  epr:                                    5
% 1.77/1.03  horn:                                   25
% 1.77/1.03  ground:                                 8
% 1.77/1.03  unary:                                  12
% 1.77/1.03  binary:                                 6
% 1.77/1.03  lits:                                   52
% 1.77/1.03  lits_eq:                                21
% 1.77/1.03  fd_pure:                                0
% 1.77/1.03  fd_pseudo:                              0
% 1.77/1.03  fd_cond:                                2
% 1.77/1.03  fd_pseudo_cond:                         1
% 1.77/1.03  ac_symbols:                             0
% 1.77/1.03  
% 1.77/1.03  ------ Propositional Solver
% 1.77/1.03  
% 1.77/1.03  prop_solver_calls:                      27
% 1.77/1.03  prop_fast_solver_calls:                 742
% 1.77/1.03  smt_solver_calls:                       0
% 1.77/1.03  smt_fast_solver_calls:                  0
% 1.77/1.03  prop_num_of_clauses:                    1090
% 1.77/1.03  prop_preprocess_simplified:             5072
% 1.77/1.03  prop_fo_subsumed:                       9
% 1.77/1.03  prop_solver_time:                       0.
% 1.77/1.03  smt_solver_time:                        0.
% 1.77/1.03  smt_fast_solver_time:                   0.
% 1.77/1.03  prop_fast_solver_time:                  0.
% 1.77/1.03  prop_unsat_core_time:                   0.
% 1.77/1.03  
% 1.77/1.03  ------ QBF
% 1.77/1.03  
% 1.77/1.03  qbf_q_res:                              0
% 1.77/1.03  qbf_num_tautologies:                    0
% 1.77/1.03  qbf_prep_cycles:                        0
% 1.77/1.03  
% 1.77/1.03  ------ BMC1
% 1.77/1.03  
% 1.77/1.03  bmc1_current_bound:                     -1
% 1.77/1.03  bmc1_last_solved_bound:                 -1
% 1.77/1.03  bmc1_unsat_core_size:                   -1
% 1.77/1.03  bmc1_unsat_core_parents_size:           -1
% 1.77/1.03  bmc1_merge_next_fun:                    0
% 1.77/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.77/1.03  
% 1.77/1.03  ------ Instantiation
% 1.77/1.03  
% 1.77/1.03  inst_num_of_clauses:                    358
% 1.77/1.03  inst_num_in_passive:                    180
% 1.77/1.03  inst_num_in_active:                     154
% 1.77/1.03  inst_num_in_unprocessed:                24
% 1.77/1.03  inst_num_of_loops:                      210
% 1.77/1.03  inst_num_of_learning_restarts:          0
% 1.77/1.03  inst_num_moves_active_passive:          54
% 1.77/1.03  inst_lit_activity:                      0
% 1.77/1.03  inst_lit_activity_moves:                0
% 1.77/1.03  inst_num_tautologies:                   0
% 1.77/1.03  inst_num_prop_implied:                  0
% 1.77/1.03  inst_num_existing_simplified:           0
% 1.77/1.03  inst_num_eq_res_simplified:             0
% 1.77/1.03  inst_num_child_elim:                    0
% 1.77/1.03  inst_num_of_dismatching_blockings:      47
% 1.77/1.03  inst_num_of_non_proper_insts:           284
% 1.77/1.03  inst_num_of_duplicates:                 0
% 1.77/1.03  inst_inst_num_from_inst_to_res:         0
% 1.77/1.03  inst_dismatching_checking_time:         0.
% 1.77/1.03  
% 1.77/1.03  ------ Resolution
% 1.77/1.03  
% 1.77/1.03  res_num_of_clauses:                     0
% 1.77/1.03  res_num_in_passive:                     0
% 1.77/1.03  res_num_in_active:                      0
% 1.77/1.03  res_num_of_loops:                       141
% 1.77/1.03  res_forward_subset_subsumed:            15
% 1.77/1.03  res_backward_subset_subsumed:           0
% 1.77/1.03  res_forward_subsumed:                   0
% 1.77/1.03  res_backward_subsumed:                  0
% 1.77/1.03  res_forward_subsumption_resolution:     1
% 1.77/1.03  res_backward_subsumption_resolution:    0
% 1.77/1.03  res_clause_to_clause_subsumption:       170
% 1.77/1.03  res_orphan_elimination:                 0
% 1.77/1.03  res_tautology_del:                      36
% 1.77/1.03  res_num_eq_res_simplified:              0
% 1.77/1.03  res_num_sel_changes:                    0
% 1.77/1.03  res_moves_from_active_to_pass:          0
% 1.77/1.03  
% 1.77/1.03  ------ Superposition
% 1.77/1.03  
% 1.77/1.03  sup_time_total:                         0.
% 1.77/1.03  sup_time_generating:                    0.
% 1.77/1.03  sup_time_sim_full:                      0.
% 1.77/1.03  sup_time_sim_immed:                     0.
% 1.77/1.03  
% 1.77/1.03  sup_num_of_clauses:                     38
% 1.77/1.03  sup_num_in_active:                      26
% 1.77/1.03  sup_num_in_passive:                     12
% 1.77/1.03  sup_num_of_loops:                       41
% 1.77/1.03  sup_fw_superposition:                   25
% 1.77/1.03  sup_bw_superposition:                   13
% 1.77/1.03  sup_immediate_simplified:               12
% 1.77/1.03  sup_given_eliminated:                   0
% 1.77/1.03  comparisons_done:                       0
% 1.77/1.03  comparisons_avoided:                    0
% 1.77/1.03  
% 1.77/1.03  ------ Simplifications
% 1.77/1.03  
% 1.77/1.03  
% 1.77/1.03  sim_fw_subset_subsumed:                 4
% 1.77/1.03  sim_bw_subset_subsumed:                 2
% 1.77/1.03  sim_fw_subsumed:                        3
% 1.77/1.03  sim_bw_subsumed:                        0
% 1.77/1.03  sim_fw_subsumption_res:                 0
% 1.77/1.03  sim_bw_subsumption_res:                 0
% 1.77/1.03  sim_tautology_del:                      2
% 1.77/1.03  sim_eq_tautology_del:                   3
% 1.77/1.03  sim_eq_res_simp:                        1
% 1.77/1.03  sim_fw_demodulated:                     8
% 1.77/1.03  sim_bw_demodulated:                     16
% 1.77/1.03  sim_light_normalised:                   5
% 1.77/1.03  sim_joinable_taut:                      0
% 1.77/1.03  sim_joinable_simp:                      0
% 1.77/1.03  sim_ac_normalised:                      0
% 1.77/1.03  sim_smt_subsumption:                    0
% 1.77/1.03  
%------------------------------------------------------------------------------
