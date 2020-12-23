%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:37 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  206 (9304 expanded)
%              Number of clauses        :  133 (3089 expanded)
%              Number of leaves         :   18 (1768 expanded)
%              Depth                    :   30
%              Number of atoms          :  614 (47820 expanded)
%              Number of equality atoms :  266 (8691 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f43])).

fof(f75,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_723,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_32])).

cnf(c_1756,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1759,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3096,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1756,c_1759])).

cnf(c_3173,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_723,c_3096])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1758,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2717,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1756,c_1758])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2718,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2717,c_30])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_502,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_503,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_505,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_34])).

cnf(c_1751,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1815,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1874,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_1965,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1751,c_34,c_32,c_503,c_1874])).

cnf(c_2723,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2718,c_1965])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1757,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3595,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2723,c_1757])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_516,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_519,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_34])).

cnf(c_1750,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_1962,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1750,c_34,c_32,c_517,c_1874])).

cnf(c_3600,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3595,c_1962])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1826,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1827,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_1875,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2546,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2547,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2546])).

cnf(c_3907,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3600,c_35,c_37,c_1827,c_1875,c_2547])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_731,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_732,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_7])).

cnf(c_464,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_15])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_744,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_732,c_15,c_465])).

cnf(c_1741,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_748,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_2557,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_35,c_37,c_748,c_1827,c_1875])).

cnf(c_2558,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2557])).

cnf(c_2561,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2558,c_1965])).

cnf(c_2722,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2718,c_2561])).

cnf(c_2724,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2722])).

cnf(c_3917,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3907,c_2724])).

cnf(c_4999,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3173,c_3917])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3814,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3815,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3814])).

cnf(c_5413,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4999,c_3815])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_591,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_575,c_26])).

cnf(c_1748,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_3555,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_1748])).

cnf(c_3723,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3555,c_35,c_37,c_1875])).

cnf(c_5430,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5413,c_3723])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_113,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_119,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1084,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1850,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_1851,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1850])).

cnf(c_1853,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_6474,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5430,c_115])).

cnf(c_6475,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6474])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_481,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_482,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_34])).

cnf(c_1752,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_488,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_2014,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1752,c_37,c_488,c_1875])).

cnf(c_2015,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2014])).

cnf(c_6480,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6475,c_2015])).

cnf(c_5936,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5937,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5936])).

cnf(c_6478,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6475,c_3917])).

cnf(c_6492,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_5937,c_6478])).

cnf(c_6505,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6492,c_3917])).

cnf(c_1767,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6510,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6492,c_2015])).

cnf(c_1766,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_17,c_9])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_17,c_15,c_9])).

cnf(c_1754,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_5002,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1754])).

cnf(c_6807,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1766,c_5002])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2622,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1760])).

cnf(c_5337,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_2622])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1763,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5345,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_5337,c_1763])).

cnf(c_6810,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6807,c_5345])).

cnf(c_5440,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5413,c_2718])).

cnf(c_6502,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6492,c_5440])).

cnf(c_6811,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6810,c_6502])).

cnf(c_7147,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6510,c_6811])).

cnf(c_7151,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1767,c_7147])).

cnf(c_7152,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1766,c_7147])).

cnf(c_7276,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7151,c_7152])).

cnf(c_7837,plain,
    ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6505,c_7276])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7837,c_5937])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:07:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         true
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     num_symb
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       true
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     true
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_input_bw                          []
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 31
% 3.59/0.98  conjectures                             3
% 3.59/0.98  EPR                                     4
% 3.59/0.98  Horn                                    27
% 3.59/0.98  unary                                   5
% 3.59/0.98  binary                                  11
% 3.59/0.98  lits                                    86
% 3.59/0.98  lits eq                                 32
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 2
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Schedule dynamic 5 is on 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.99  --symbol_type_check                     false
% 3.59/0.99  --clausify_out                          false
% 3.59/0.99  --sig_cnt_out                           false
% 3.59/0.99  --trig_cnt_out                          false
% 3.59/0.99  --trig_cnt_out_tolerance                1.
% 3.59/0.99  --trig_cnt_out_sk_spl                   false
% 3.59/0.99  --abstr_cl_out                          false
% 3.59/0.99  
% 3.59/0.99  ------ Global Options
% 3.59/0.99  
% 3.59/0.99  --schedule                              default
% 3.59/0.99  --add_important_lit                     false
% 3.59/0.99  --prop_solver_per_cl                    1000
% 3.59/0.99  --min_unsat_core                        false
% 3.59/0.99  --soft_assumptions                      false
% 3.59/0.99  --soft_lemma_size                       3
% 3.59/0.99  --prop_impl_unit_size                   0
% 3.59/0.99  --prop_impl_unit                        []
% 3.59/0.99  --share_sel_clauses                     true
% 3.59/0.99  --reset_solvers                         false
% 3.59/0.99  --bc_imp_inh                            [conj_cone]
% 3.59/0.99  --conj_cone_tolerance                   3.
% 3.59/0.99  --extra_neg_conj                        none
% 3.59/0.99  --large_theory_mode                     true
% 3.59/0.99  --prolific_symb_bound                   200
% 3.59/0.99  --lt_threshold                          2000
% 3.59/0.99  --clause_weak_htbl                      true
% 3.59/0.99  --gc_record_bc_elim                     false
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing Options
% 3.59/0.99  
% 3.59/0.99  --preprocessing_flag                    true
% 3.59/0.99  --time_out_prep_mult                    0.1
% 3.59/0.99  --splitting_mode                        input
% 3.59/0.99  --splitting_grd                         true
% 3.59/0.99  --splitting_cvd                         false
% 3.59/0.99  --splitting_cvd_svl                     false
% 3.59/0.99  --splitting_nvd                         32
% 3.59/0.99  --sub_typing                            true
% 3.59/0.99  --prep_gs_sim                           true
% 3.59/0.99  --prep_unflatten                        true
% 3.59/0.99  --prep_res_sim                          true
% 3.59/0.99  --prep_upred                            true
% 3.59/0.99  --prep_sem_filter                       exhaustive
% 3.59/0.99  --prep_sem_filter_out                   false
% 3.59/0.99  --pred_elim                             true
% 3.59/0.99  --res_sim_input                         true
% 3.59/0.99  --eq_ax_congr_red                       true
% 3.59/0.99  --pure_diseq_elim                       true
% 3.59/0.99  --brand_transform                       false
% 3.59/0.99  --non_eq_to_eq                          false
% 3.59/0.99  --prep_def_merge                        true
% 3.59/0.99  --prep_def_merge_prop_impl              false
% 3.59/0.99  --prep_def_merge_mbd                    true
% 3.59/0.99  --prep_def_merge_tr_red                 false
% 3.59/0.99  --prep_def_merge_tr_cl                  false
% 3.59/0.99  --smt_preprocessing                     true
% 3.59/0.99  --smt_ac_axioms                         fast
% 3.59/0.99  --preprocessed_out                      false
% 3.59/0.99  --preprocessed_stats                    false
% 3.59/0.99  
% 3.59/0.99  ------ Abstraction refinement Options
% 3.59/0.99  
% 3.59/0.99  --abstr_ref                             []
% 3.59/0.99  --abstr_ref_prep                        false
% 3.59/0.99  --abstr_ref_until_sat                   false
% 3.59/0.99  --abstr_ref_sig_restrict                funpre
% 3.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.99  --abstr_ref_under                       []
% 3.59/0.99  
% 3.59/0.99  ------ SAT Options
% 3.59/0.99  
% 3.59/0.99  --sat_mode                              false
% 3.59/0.99  --sat_fm_restart_options                ""
% 3.59/0.99  --sat_gr_def                            false
% 3.59/0.99  --sat_epr_types                         true
% 3.59/0.99  --sat_non_cyclic_types                  false
% 3.59/0.99  --sat_finite_models                     false
% 3.59/0.99  --sat_fm_lemmas                         false
% 3.59/0.99  --sat_fm_prep                           false
% 3.59/0.99  --sat_fm_uc_incr                        true
% 3.59/0.99  --sat_out_model                         small
% 3.59/0.99  --sat_out_clauses                       false
% 3.59/0.99  
% 3.59/0.99  ------ QBF Options
% 3.59/0.99  
% 3.59/0.99  --qbf_mode                              false
% 3.59/0.99  --qbf_elim_univ                         false
% 3.59/0.99  --qbf_dom_inst                          none
% 3.59/0.99  --qbf_dom_pre_inst                      false
% 3.59/0.99  --qbf_sk_in                             false
% 3.59/0.99  --qbf_pred_elim                         true
% 3.59/0.99  --qbf_split                             512
% 3.59/0.99  
% 3.59/0.99  ------ BMC1 Options
% 3.59/0.99  
% 3.59/0.99  --bmc1_incremental                      false
% 3.59/0.99  --bmc1_axioms                           reachable_all
% 3.59/0.99  --bmc1_min_bound                        0
% 3.59/0.99  --bmc1_max_bound                        -1
% 3.59/0.99  --bmc1_max_bound_default                -1
% 3.59/0.99  --bmc1_symbol_reachability              true
% 3.59/0.99  --bmc1_property_lemmas                  false
% 3.59/0.99  --bmc1_k_induction                      false
% 3.59/0.99  --bmc1_non_equiv_states                 false
% 3.59/0.99  --bmc1_deadlock                         false
% 3.59/0.99  --bmc1_ucm                              false
% 3.59/0.99  --bmc1_add_unsat_core                   none
% 3.59/0.99  --bmc1_unsat_core_children              false
% 3.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.99  --bmc1_out_stat                         full
% 3.59/0.99  --bmc1_ground_init                      false
% 3.59/0.99  --bmc1_pre_inst_next_state              false
% 3.59/0.99  --bmc1_pre_inst_state                   false
% 3.59/0.99  --bmc1_pre_inst_reach_state             false
% 3.59/0.99  --bmc1_out_unsat_core                   false
% 3.59/0.99  --bmc1_aig_witness_out                  false
% 3.59/0.99  --bmc1_verbose                          false
% 3.59/0.99  --bmc1_dump_clauses_tptp                false
% 3.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.99  --bmc1_dump_file                        -
% 3.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.99  --bmc1_ucm_extend_mode                  1
% 3.59/0.99  --bmc1_ucm_init_mode                    2
% 3.59/0.99  --bmc1_ucm_cone_mode                    none
% 3.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.99  --bmc1_ucm_relax_model                  4
% 3.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.99  --bmc1_ucm_layered_model                none
% 3.59/0.99  --bmc1_ucm_max_lemma_size               10
% 3.59/0.99  
% 3.59/0.99  ------ AIG Options
% 3.59/0.99  
% 3.59/0.99  --aig_mode                              false
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation Options
% 3.59/0.99  
% 3.59/0.99  --instantiation_flag                    true
% 3.59/0.99  --inst_sos_flag                         true
% 3.59/0.99  --inst_sos_phase                        true
% 3.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel_side                     none
% 3.59/0.99  --inst_solver_per_active                1400
% 3.59/0.99  --inst_solver_calls_frac                1.
% 3.59/0.99  --inst_passive_queue_type               priority_queues
% 3.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.99  --inst_passive_queues_freq              [25;2]
% 3.59/0.99  --inst_dismatching                      true
% 3.59/0.99  --inst_eager_unprocessed_to_passive     true
% 3.59/0.99  --inst_prop_sim_given                   true
% 3.59/0.99  --inst_prop_sim_new                     false
% 3.59/0.99  --inst_subs_new                         false
% 3.59/0.99  --inst_eq_res_simp                      false
% 3.59/0.99  --inst_subs_given                       false
% 3.59/0.99  --inst_orphan_elimination               true
% 3.59/0.99  --inst_learning_loop_flag               true
% 3.59/0.99  --inst_learning_start                   3000
% 3.59/0.99  --inst_learning_factor                  2
% 3.59/0.99  --inst_start_prop_sim_after_learn       3
% 3.59/0.99  --inst_sel_renew                        solver
% 3.59/0.99  --inst_lit_activity_flag                true
% 3.59/0.99  --inst_restr_to_given                   false
% 3.59/0.99  --inst_activity_threshold               500
% 3.59/0.99  --inst_out_proof                        true
% 3.59/0.99  
% 3.59/0.99  ------ Resolution Options
% 3.59/0.99  
% 3.59/0.99  --resolution_flag                       false
% 3.59/0.99  --res_lit_sel                           adaptive
% 3.59/0.99  --res_lit_sel_side                      none
% 3.59/0.99  --res_ordering                          kbo
% 3.59/0.99  --res_to_prop_solver                    active
% 3.59/0.99  --res_prop_simpl_new                    false
% 3.59/0.99  --res_prop_simpl_given                  true
% 3.59/0.99  --res_passive_queue_type                priority_queues
% 3.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.99  --res_passive_queues_freq               [15;5]
% 3.59/0.99  --res_forward_subs                      full
% 3.59/0.99  --res_backward_subs                     full
% 3.59/0.99  --res_forward_subs_resolution           true
% 3.59/0.99  --res_backward_subs_resolution          true
% 3.59/0.99  --res_orphan_elimination                true
% 3.59/0.99  --res_time_limit                        2.
% 3.59/0.99  --res_out_proof                         true
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Options
% 3.59/0.99  
% 3.59/0.99  --superposition_flag                    true
% 3.59/0.99  --sup_passive_queue_type                priority_queues
% 3.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.99  --demod_completeness_check              fast
% 3.59/0.99  --demod_use_ground                      true
% 3.59/0.99  --sup_to_prop_solver                    passive
% 3.59/0.99  --sup_prop_simpl_new                    true
% 3.59/0.99  --sup_prop_simpl_given                  true
% 3.59/0.99  --sup_fun_splitting                     true
% 3.59/0.99  --sup_smt_interval                      50000
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Simplification Setup
% 3.59/0.99  
% 3.59/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.99  --sup_immed_triv                        [TrivRules]
% 3.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.99  --sup_immed_bw_main                     []
% 3.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.99  --sup_input_bw                          []
% 3.59/0.99  
% 3.59/0.99  ------ Combination Options
% 3.59/0.99  
% 3.59/0.99  --comb_res_mult                         3
% 3.59/0.99  --comb_sup_mult                         2
% 3.59/0.99  --comb_inst_mult                        10
% 3.59/0.99  
% 3.59/0.99  ------ Debug Options
% 3.59/0.99  
% 3.59/0.99  --dbg_backtrace                         false
% 3.59/0.99  --dbg_dump_prop_clauses                 false
% 3.59/0.99  --dbg_dump_prop_clauses_file            -
% 3.59/0.99  --dbg_out_stat                          false
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  ------ Proving...
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  % SZS status Theorem for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  fof(f14,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f32,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f14])).
% 3.59/0.99  
% 3.59/0.99  fof(f33,plain,(
% 3.59/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(flattening,[],[f32])).
% 3.59/0.99  
% 3.59/0.99  fof(f42,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(nnf_transformation,[],[f33])).
% 3.59/0.99  
% 3.59/0.99  fof(f65,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f42])).
% 3.59/0.99  
% 3.59/0.99  fof(f16,conjecture,(
% 3.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f17,negated_conjecture,(
% 3.59/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.59/0.99    inference(negated_conjecture,[],[f16])).
% 3.59/0.99  
% 3.59/0.99  fof(f36,plain,(
% 3.59/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.59/0.99    inference(ennf_transformation,[],[f17])).
% 3.59/0.99  
% 3.59/0.99  fof(f37,plain,(
% 3.59/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.59/0.99    inference(flattening,[],[f36])).
% 3.59/0.99  
% 3.59/0.99  fof(f43,plain,(
% 3.59/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.59/0.99    introduced(choice_axiom,[])).
% 3.59/0.99  
% 3.59/0.99  fof(f44,plain,(
% 3.59/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f43])).
% 3.59/0.99  
% 3.59/0.99  fof(f75,plain,(
% 3.59/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f76,plain,(
% 3.59/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f12,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f30,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f12])).
% 3.59/0.99  
% 3.59/0.99  fof(f63,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f30])).
% 3.59/0.99  
% 3.59/0.99  fof(f13,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f31,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f13])).
% 3.59/0.99  
% 3.59/0.99  fof(f64,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f31])).
% 3.59/0.99  
% 3.59/0.99  fof(f78,plain,(
% 3.59/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f9,axiom,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f26,plain,(
% 3.59/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.59/0.99    inference(ennf_transformation,[],[f9])).
% 3.59/0.99  
% 3.59/0.99  fof(f27,plain,(
% 3.59/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(flattening,[],[f26])).
% 3.59/0.99  
% 3.59/0.99  fof(f58,plain,(
% 3.59/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f27])).
% 3.59/0.99  
% 3.59/0.99  fof(f77,plain,(
% 3.59/0.99    v2_funct_1(sK2)),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f74,plain,(
% 3.59/0.99    v1_funct_1(sK2)),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f10,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f28,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f10])).
% 3.59/0.99  
% 3.59/0.99  fof(f60,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f28])).
% 3.59/0.99  
% 3.59/0.99  fof(f15,axiom,(
% 3.59/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f34,plain,(
% 3.59/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.59/0.99    inference(ennf_transformation,[],[f15])).
% 3.59/0.99  
% 3.59/0.99  fof(f35,plain,(
% 3.59/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(flattening,[],[f34])).
% 3.59/0.99  
% 3.59/0.99  fof(f73,plain,(
% 3.59/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f35])).
% 3.59/0.99  
% 3.59/0.99  fof(f59,plain,(
% 3.59/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f27])).
% 3.59/0.99  
% 3.59/0.99  fof(f7,axiom,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f22,plain,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.59/0.99    inference(ennf_transformation,[],[f7])).
% 3.59/0.99  
% 3.59/0.99  fof(f23,plain,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(flattening,[],[f22])).
% 3.59/0.99  
% 3.59/0.99  fof(f56,plain,(
% 3.59/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f23])).
% 3.59/0.99  
% 3.59/0.99  fof(f55,plain,(
% 3.59/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f23])).
% 3.59/0.99  
% 3.59/0.99  fof(f72,plain,(
% 3.59/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f35])).
% 3.59/0.99  
% 3.59/0.99  fof(f79,plain,(
% 3.59/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.59/0.99    inference(cnf_transformation,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f11,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f29,plain,(
% 3.59/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f11])).
% 3.59/0.99  
% 3.59/0.99  fof(f62,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f29])).
% 3.59/0.99  
% 3.59/0.99  fof(f4,axiom,(
% 3.59/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f18,plain,(
% 3.59/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(ennf_transformation,[],[f4])).
% 3.59/0.99  
% 3.59/0.99  fof(f41,plain,(
% 3.59/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(nnf_transformation,[],[f18])).
% 3.59/0.99  
% 3.59/0.99  fof(f51,plain,(
% 3.59/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f41])).
% 3.59/0.99  
% 3.59/0.99  fof(f1,axiom,(
% 3.59/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f38,plain,(
% 3.59/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.99    inference(nnf_transformation,[],[f1])).
% 3.59/0.99  
% 3.59/0.99  fof(f39,plain,(
% 3.59/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.99    inference(flattening,[],[f38])).
% 3.59/0.99  
% 3.59/0.99  fof(f46,plain,(
% 3.59/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.99    inference(cnf_transformation,[],[f39])).
% 3.59/0.99  
% 3.59/0.99  fof(f80,plain,(
% 3.59/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.99    inference(equality_resolution,[],[f46])).
% 3.59/0.99  
% 3.59/0.99  fof(f69,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f42])).
% 3.59/0.99  
% 3.59/0.99  fof(f84,plain,(
% 3.59/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.59/0.99    inference(equality_resolution,[],[f69])).
% 3.59/0.99  
% 3.59/0.99  fof(f2,axiom,(
% 3.59/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f48,plain,(
% 3.59/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f2])).
% 3.59/0.99  
% 3.59/0.99  fof(f47,plain,(
% 3.59/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f39])).
% 3.59/0.99  
% 3.59/0.99  fof(f8,axiom,(
% 3.59/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f24,plain,(
% 3.59/0.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.59/0.99    inference(ennf_transformation,[],[f8])).
% 3.59/0.99  
% 3.59/0.99  fof(f25,plain,(
% 3.59/0.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(flattening,[],[f24])).
% 3.59/0.99  
% 3.59/0.99  fof(f57,plain,(
% 3.59/0.99    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f25])).
% 3.59/0.99  
% 3.59/0.99  fof(f3,axiom,(
% 3.59/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f40,plain,(
% 3.59/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/0.99    inference(nnf_transformation,[],[f3])).
% 3.59/0.99  
% 3.59/0.99  fof(f50,plain,(
% 3.59/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f40])).
% 3.59/0.99  
% 3.59/0.99  fof(f61,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f29])).
% 3.59/0.99  
% 3.59/0.99  fof(f6,axiom,(
% 3.59/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f20,plain,(
% 3.59/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.59/0.99    inference(ennf_transformation,[],[f6])).
% 3.59/0.99  
% 3.59/0.99  fof(f21,plain,(
% 3.59/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(flattening,[],[f20])).
% 3.59/0.99  
% 3.59/0.99  fof(f54,plain,(
% 3.59/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f21])).
% 3.59/0.99  
% 3.59/0.99  fof(f5,axiom,(
% 3.59/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f19,plain,(
% 3.59/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.99    inference(ennf_transformation,[],[f5])).
% 3.59/0.99  
% 3.59/0.99  fof(f53,plain,(
% 3.59/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f19])).
% 3.59/0.99  
% 3.59/0.99  cnf(c_25,plain,
% 3.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.99      | k1_xboole_0 = X2 ),
% 3.59/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_33,negated_conjecture,
% 3.59/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.59/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_720,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.99      | sK0 != X1
% 3.59/0.99      | sK1 != X2
% 3.59/0.99      | sK2 != X0
% 3.59/0.99      | k1_xboole_0 = X2 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_721,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.59/0.99      | k1_xboole_0 = sK1 ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_720]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_32,negated_conjecture,
% 3.59/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.59/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_723,plain,
% 3.59/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_721,c_32]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1756,plain,
% 3.59/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_18,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1759,plain,
% 3.59/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3096,plain,
% 3.59/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1756,c_1759]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3173,plain,
% 3.59/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_723,c_3096]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_19,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1758,plain,
% 3.59/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2717,plain,
% 3.59/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1756,c_1758]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_30,negated_conjecture,
% 3.59/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.59/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2718,plain,
% 3.59/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_2717,c_30]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_14,plain,
% 3.59/0.99      ( ~ v2_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_31,negated_conjecture,
% 3.59/0.99      ( v2_funct_1(sK2) ),
% 3.59/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_502,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.59/0.99      | sK2 != X0 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_503,plain,
% 3.59/0.99      ( ~ v1_funct_1(sK2)
% 3.59/0.99      | ~ v1_relat_1(sK2)
% 3.59/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_34,negated_conjecture,
% 3.59/0.99      ( v1_funct_1(sK2) ),
% 3.59/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_505,plain,
% 3.59/0.99      ( ~ v1_relat_1(sK2)
% 3.59/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_503,c_34]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1751,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_15,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1815,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.99      | v1_relat_1(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1874,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.99      | v1_relat_1(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1815]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1965,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_1751,c_34,c_32,c_503,c_1874]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2723,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_2718,c_1965]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_26,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1757,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.59/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3595,plain,
% 3.59/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.59/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.59/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.59/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2723,c_1757]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_13,plain,
% 3.59/0.99      ( ~ v2_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_516,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.59/0.99      | sK2 != X0 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_517,plain,
% 3.59/0.99      ( ~ v1_funct_1(sK2)
% 3.59/0.99      | ~ v1_relat_1(sK2)
% 3.59/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_516]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_519,plain,
% 3.59/0.99      ( ~ v1_relat_1(sK2)
% 3.59/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_517,c_34]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1750,plain,
% 3.59/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1962,plain,
% 3.59/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_1750,c_34,c_32,c_517,c_1874]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3600,plain,
% 3.59/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.59/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.59/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.59/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_3595,c_1962]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_35,plain,
% 3.59/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_37,plain,
% 3.59/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_10,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1826,plain,
% 3.59/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.59/0.99      | ~ v1_funct_1(sK2)
% 3.59/0.99      | ~ v1_relat_1(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1827,plain,
% 3.59/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.59/0.99      | v1_funct_1(sK2) != iProver_top
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1875,plain,
% 3.59/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.59/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2546,plain,
% 3.59/0.99      ( ~ v1_funct_1(sK2)
% 3.59/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.59/0.99      | ~ v1_relat_1(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2547,plain,
% 3.59/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.59/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2546]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3907,plain,
% 3.59/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.59/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_3600,c_35,c_37,c_1827,c_1875,c_2547]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_27,plain,
% 3.59/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_29,negated_conjecture,
% 3.59/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.59/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.59/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.59/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_731,plain,
% 3.59/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k1_relat_1(X0) != sK1
% 3.59/0.99      | k2_funct_1(sK2) != X0
% 3.59/0.99      | sK0 != X1 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_732,plain,
% 3.59/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.59/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.59/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.59/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_731]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_16,plain,
% 3.59/0.99      ( v5_relat_1(X0,X1)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.59/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7,plain,
% 3.59/0.99      ( ~ v5_relat_1(X0,X1)
% 3.59/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_460,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(resolution,[status(thm)],[c_16,c_7]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_464,plain,
% 3.59/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_460,c_15]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_465,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_464]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_744,plain,
% 3.59/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.59/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.59/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.59/0.99      inference(forward_subsumption_resolution,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_732,c_15,c_465]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1741,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.59/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.59/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_748,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.59/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.59/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2557,plain,
% 3.59/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.59/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_1741,c_35,c_37,c_748,c_1827,c_1875]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2558,plain,
% 3.59/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.59/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_2557]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2561,plain,
% 3.59/0.99      ( k2_relat_1(sK2) != sK1
% 3.59/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_2558,c_1965]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2722,plain,
% 3.59/0.99      ( sK1 != sK1
% 3.59/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_2718,c_2561]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2724,plain,
% 3.59/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.59/0.99      inference(equality_resolution_simp,[status(thm)],[c_2722]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3917,plain,
% 3.59/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_3907,c_2724]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4999,plain,
% 3.59/0.99      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_3173,c_3917]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1,plain,
% 3.59/0.99      ( r1_tarski(X0,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3814,plain,
% 3.59/0.99      ( r1_tarski(sK0,sK0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3815,plain,
% 3.59/0.99      ( r1_tarski(sK0,sK0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3814]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5413,plain,
% 3.59/0.99      ( sK1 = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_4999,c_3815]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_21,plain,
% 3.59/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.59/0.99      | k1_xboole_0 = X1
% 3.59/0.99      | k1_xboole_0 = X0 ),
% 3.59/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_574,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.59/0.99      | ~ v1_funct_1(X2)
% 3.59/0.99      | ~ v1_relat_1(X2)
% 3.59/0.99      | X2 != X0
% 3.59/0.99      | k1_relat_1(X2) != X1
% 3.59/0.99      | k1_xboole_0 != X3
% 3.59/0.99      | k1_xboole_0 = X0
% 3.59/0.99      | k1_xboole_0 = X1 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_575,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.59/0.99      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k1_xboole_0 = X0
% 3.59/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_591,plain,
% 3.59/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k1_xboole_0 = X0
% 3.59/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.59/0.99      inference(forward_subsumption_resolution,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_575,c_26]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1748,plain,
% 3.59/0.99      ( k1_xboole_0 = X0
% 3.59/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.59/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3555,plain,
% 3.59/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.59/0.99      | sK2 = k1_xboole_0
% 3.59/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.59/0.99      | v1_funct_1(sK2) != iProver_top
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2718,c_1748]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3723,plain,
% 3.59/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.59/0.99      | sK2 = k1_xboole_0
% 3.59/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_3555,c_35,c_37,c_1875]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5430,plain,
% 3.59/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.59/0.99      | sK2 = k1_xboole_0
% 3.59/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_5413,c_3723]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_114,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_113,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_115,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_113]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_0,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.59/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_119,plain,
% 3.59/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.59/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1084,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/0.99      theory(equality) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1850,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,X1)
% 3.59/0.99      | r1_tarski(sK1,k1_xboole_0)
% 3.59/0.99      | sK1 != X0
% 3.59/0.99      | k1_xboole_0 != X1 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1084]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1851,plain,
% 3.59/0.99      ( sK1 != X0
% 3.59/0.99      | k1_xboole_0 != X1
% 3.59/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.59/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1850]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1853,plain,
% 3.59/0.99      ( sK1 != k1_xboole_0
% 3.59/0.99      | k1_xboole_0 != k1_xboole_0
% 3.59/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.59/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1851]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6474,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_5430,c_115]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6475,plain,
% 3.59/0.99      ( k1_relat_1(sK2) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_6474]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_12,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.59/0.99      | ~ v2_funct_1(X1)
% 3.59/0.99      | ~ v1_funct_1(X1)
% 3.59/0.99      | ~ v1_relat_1(X1)
% 3.59/0.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.59/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_481,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.59/0.99      | ~ v1_funct_1(X1)
% 3.59/0.99      | ~ v1_relat_1(X1)
% 3.59/0.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.59/0.99      | sK2 != X1 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_482,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.59/0.99      | ~ v1_funct_1(sK2)
% 3.59/0.99      | ~ v1_relat_1(sK2)
% 3.59/0.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_486,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.59/0.99      | ~ v1_relat_1(sK2)
% 3.59/0.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_482,c_34]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1752,plain,
% 3.59/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.59/0.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_488,plain,
% 3.59/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.59/0.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.59/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2014,plain,
% 3.59/0.99      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.59/0.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_1752,c_37,c_488,c_1875]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2015,plain,
% 3.59/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.59/0.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_2014]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6480,plain,
% 3.59/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.59/0.99      | sK2 = k1_xboole_0
% 3.59/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_6475,c_2015]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5936,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,sK0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5937,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_5936]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6478,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_6475,c_3917]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6492,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_6480,c_5937,c_6478]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6505,plain,
% 3.59/0.99      ( r1_tarski(k1_relat_1(k1_xboole_0),sK0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_6492,c_3917]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1767,plain,
% 3.59/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6510,plain,
% 3.59/0.99      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
% 3.59/0.99      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_6492,c_2015]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1766,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1765,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.59/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_17,plain,
% 3.59/0.99      ( v4_relat_1(X0,X1)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.59/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9,plain,
% 3.59/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.59/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_440,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.59/0.99      inference(resolution,[status(thm)],[c_17,c_9]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_444,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_440,c_17,c_15,c_9]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1754,plain,
% 3.59/0.99      ( k7_relat_1(X0,X1) = X0
% 3.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5002,plain,
% 3.59/0.99      ( k7_relat_1(X0,X1) = X0
% 3.59/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1765,c_1754]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6807,plain,
% 3.59/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1766,c_5002]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1760,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2622,plain,
% 3.59/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1765,c_1760]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5337,plain,
% 3.59/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1766,c_2622]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8,plain,
% 3.59/0.99      ( ~ v1_relat_1(X0)
% 3.59/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.59/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1763,plain,
% 3.59/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5345,plain,
% 3.59/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_5337,c_1763]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6810,plain,
% 3.59/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_6807,c_5345]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5440,plain,
% 3.59/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_5413,c_2718]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6502,plain,
% 3.59/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_6492,c_5440]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6811,plain,
% 3.59/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_6810,c_6502]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7147,plain,
% 3.59/0.99      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
% 3.59/0.99      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_6510,c_6811]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7151,plain,
% 3.59/0.99      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1767,c_7147]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7152,plain,
% 3.59/0.99      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1766,c_7147]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7276,plain,
% 3.59/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_7151,c_7152]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7837,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_6505,c_7276]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(contradiction,plain,
% 3.59/0.99      ( $false ),
% 3.59/0.99      inference(minisat,[status(thm)],[c_7837,c_5937]) ).
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  ------                               Statistics
% 3.59/0.99  
% 3.59/0.99  ------ General
% 3.59/0.99  
% 3.59/0.99  abstr_ref_over_cycles:                  0
% 3.59/0.99  abstr_ref_under_cycles:                 0
% 3.59/0.99  gc_basic_clause_elim:                   0
% 3.59/0.99  forced_gc_time:                         0
% 3.59/0.99  parsing_time:                           0.01
% 3.59/0.99  unif_index_cands_time:                  0.
% 3.59/0.99  unif_index_add_time:                    0.
% 3.59/0.99  orderings_time:                         0.
% 3.59/0.99  out_proof_time:                         0.015
% 3.59/0.99  total_time:                             0.253
% 3.59/0.99  num_of_symbols:                         53
% 3.59/0.99  num_of_terms:                           6395
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing
% 3.59/0.99  
% 3.59/0.99  num_of_splits:                          0
% 3.59/0.99  num_of_split_atoms:                     0
% 3.59/0.99  num_of_reused_defs:                     0
% 3.59/0.99  num_eq_ax_congr_red:                    17
% 3.59/0.99  num_of_sem_filtered_clauses:            1
% 3.59/0.99  num_of_subtypes:                        0
% 3.59/0.99  monotx_restored_types:                  0
% 3.59/0.99  sat_num_of_epr_types:                   0
% 3.59/0.99  sat_num_of_non_cyclic_types:            0
% 3.59/0.99  sat_guarded_non_collapsed_types:        0
% 3.59/0.99  num_pure_diseq_elim:                    0
% 3.59/0.99  simp_replaced_by:                       0
% 3.59/0.99  res_preprocessed:                       157
% 3.59/0.99  prep_upred:                             0
% 3.59/0.99  prep_unflattend:                        46
% 3.59/0.99  smt_new_axioms:                         0
% 3.59/0.99  pred_elim_cands:                        4
% 3.59/0.99  pred_elim:                              4
% 3.59/0.99  pred_elim_cl:                           2
% 3.59/0.99  pred_elim_cycles:                       6
% 3.59/0.99  merged_defs:                            8
% 3.59/0.99  merged_defs_ncl:                        0
% 3.59/0.99  bin_hyper_res:                          8
% 3.59/0.99  prep_cycles:                            4
% 3.59/0.99  pred_elim_time:                         0.009
% 3.59/0.99  splitting_time:                         0.
% 3.59/0.99  sem_filter_time:                        0.
% 3.59/0.99  monotx_time:                            0.
% 3.59/0.99  subtype_inf_time:                       0.
% 3.59/0.99  
% 3.59/0.99  ------ Problem properties
% 3.59/0.99  
% 3.59/0.99  clauses:                                31
% 3.59/0.99  conjectures:                            3
% 3.59/0.99  epr:                                    4
% 3.59/0.99  horn:                                   27
% 3.59/0.99  ground:                                 13
% 3.59/0.99  unary:                                  5
% 3.59/0.99  binary:                                 11
% 3.59/0.99  lits:                                   86
% 3.59/0.99  lits_eq:                                32
% 3.59/0.99  fd_pure:                                0
% 3.59/0.99  fd_pseudo:                              0
% 3.59/0.99  fd_cond:                                2
% 3.59/0.99  fd_pseudo_cond:                         1
% 3.59/0.99  ac_symbols:                             0
% 3.59/0.99  
% 3.59/0.99  ------ Propositional Solver
% 3.59/0.99  
% 3.59/0.99  prop_solver_calls:                      32
% 3.59/0.99  prop_fast_solver_calls:                 1273
% 3.59/0.99  smt_solver_calls:                       0
% 3.59/0.99  smt_fast_solver_calls:                  0
% 3.59/0.99  prop_num_of_clauses:                    3231
% 3.59/0.99  prop_preprocess_simplified:             7589
% 3.59/0.99  prop_fo_subsumed:                       40
% 3.59/0.99  prop_solver_time:                       0.
% 3.59/0.99  smt_solver_time:                        0.
% 3.59/0.99  smt_fast_solver_time:                   0.
% 3.59/0.99  prop_fast_solver_time:                  0.
% 3.59/0.99  prop_unsat_core_time:                   0.001
% 3.59/0.99  
% 3.59/0.99  ------ QBF
% 3.59/0.99  
% 3.59/0.99  qbf_q_res:                              0
% 3.59/0.99  qbf_num_tautologies:                    0
% 3.59/0.99  qbf_prep_cycles:                        0
% 3.59/0.99  
% 3.59/0.99  ------ BMC1
% 3.59/0.99  
% 3.59/0.99  bmc1_current_bound:                     -1
% 3.59/0.99  bmc1_last_solved_bound:                 -1
% 3.59/0.99  bmc1_unsat_core_size:                   -1
% 3.59/0.99  bmc1_unsat_core_parents_size:           -1
% 3.59/0.99  bmc1_merge_next_fun:                    0
% 3.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation
% 3.59/0.99  
% 3.59/0.99  inst_num_of_clauses:                    972
% 3.59/0.99  inst_num_in_passive:                    195
% 3.59/0.99  inst_num_in_active:                     424
% 3.59/0.99  inst_num_in_unprocessed:                353
% 3.59/0.99  inst_num_of_loops:                      570
% 3.59/0.99  inst_num_of_learning_restarts:          0
% 3.59/0.99  inst_num_moves_active_passive:          141
% 3.59/0.99  inst_lit_activity:                      0
% 3.59/0.99  inst_lit_activity_moves:                0
% 3.59/0.99  inst_num_tautologies:                   0
% 3.59/0.99  inst_num_prop_implied:                  0
% 3.59/0.99  inst_num_existing_simplified:           0
% 3.59/0.99  inst_num_eq_res_simplified:             0
% 3.59/0.99  inst_num_child_elim:                    0
% 3.59/0.99  inst_num_of_dismatching_blockings:      372
% 3.59/0.99  inst_num_of_non_proper_insts:           1188
% 3.59/0.99  inst_num_of_duplicates:                 0
% 3.59/0.99  inst_inst_num_from_inst_to_res:         0
% 3.59/0.99  inst_dismatching_checking_time:         0.
% 3.59/0.99  
% 3.59/0.99  ------ Resolution
% 3.59/0.99  
% 3.59/0.99  res_num_of_clauses:                     0
% 3.59/0.99  res_num_in_passive:                     0
% 3.59/0.99  res_num_in_active:                      0
% 3.59/0.99  res_num_of_loops:                       161
% 3.59/0.99  res_forward_subset_subsumed:            71
% 3.59/0.99  res_backward_subset_subsumed:           0
% 3.59/0.99  res_forward_subsumed:                   0
% 3.59/0.99  res_backward_subsumed:                  0
% 3.59/0.99  res_forward_subsumption_resolution:     5
% 3.59/0.99  res_backward_subsumption_resolution:    0
% 3.59/0.99  res_clause_to_clause_subsumption:       368
% 3.59/0.99  res_orphan_elimination:                 0
% 3.59/0.99  res_tautology_del:                      106
% 3.59/0.99  res_num_eq_res_simplified:              0
% 3.59/0.99  res_num_sel_changes:                    0
% 3.59/0.99  res_moves_from_active_to_pass:          0
% 3.59/0.99  
% 3.59/0.99  ------ Superposition
% 3.59/0.99  
% 3.59/0.99  sup_time_total:                         0.
% 3.59/0.99  sup_time_generating:                    0.
% 3.59/0.99  sup_time_sim_full:                      0.
% 3.59/0.99  sup_time_sim_immed:                     0.
% 3.59/0.99  
% 3.59/0.99  sup_num_of_clauses:                     91
% 3.59/0.99  sup_num_in_active:                      42
% 3.59/0.99  sup_num_in_passive:                     49
% 3.59/0.99  sup_num_of_loops:                       112
% 3.59/0.99  sup_fw_superposition:                   64
% 3.59/0.99  sup_bw_superposition:                   78
% 3.59/0.99  sup_immediate_simplified:               38
% 3.59/0.99  sup_given_eliminated:                   2
% 3.59/0.99  comparisons_done:                       0
% 3.59/0.99  comparisons_avoided:                    40
% 3.59/0.99  
% 3.59/0.99  ------ Simplifications
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  sim_fw_subset_subsumed:                 12
% 3.59/0.99  sim_bw_subset_subsumed:                 8
% 3.59/0.99  sim_fw_subsumed:                        5
% 3.59/0.99  sim_bw_subsumed:                        9
% 3.59/0.99  sim_fw_subsumption_res:                 0
% 3.59/0.99  sim_bw_subsumption_res:                 0
% 3.59/0.99  sim_tautology_del:                      5
% 3.59/0.99  sim_eq_tautology_del:                   19
% 3.59/0.99  sim_eq_res_simp:                        3
% 3.59/0.99  sim_fw_demodulated:                     2
% 3.59/0.99  sim_bw_demodulated:                     58
% 3.59/0.99  sim_light_normalised:                   32
% 3.59/0.99  sim_joinable_taut:                      0
% 3.59/0.99  sim_joinable_simp:                      0
% 3.59/0.99  sim_ac_normalised:                      0
% 3.59/0.99  sim_smt_subsumption:                    0
% 3.59/0.99  
%------------------------------------------------------------------------------
