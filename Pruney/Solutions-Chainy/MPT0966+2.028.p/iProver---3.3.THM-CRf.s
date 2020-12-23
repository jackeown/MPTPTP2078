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
% DateTime   : Thu Dec  3 12:00:36 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  210 (9382 expanded)
%              Number of clauses        :  151 (3593 expanded)
%              Number of leaves         :   16 (1688 expanded)
%              Depth                    :   34
%              Number of atoms          :  608 (48950 expanded)
%              Number of equality atoms :  363 (16190 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1294,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1285,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1288,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2736,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1285,c_1288])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1286,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3087,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2736,c_1286])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_483,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_485,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1289,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2930,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1285,c_1289])).

cnf(c_3158,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_485,c_2930])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2929,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1289])).

cnf(c_5969,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3158,c_2929])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2306,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1291])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_276,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_218])).

cnf(c_1284,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_2310,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_1284])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1290,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2534,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2310,c_1290])).

cnf(c_6330,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5969,c_2534])).

cnf(c_6331,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6330])).

cnf(c_6342,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3087,c_6331])).

cnf(c_6380,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1294,c_6342])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_155,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_32])).

cnf(c_156,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_156])).

cnf(c_470,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1278,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_6453,plain,
    ( k1_relat_1(sK4) != sK1
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6380,c_1278])).

cnf(c_6456,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6453,c_3158])).

cnf(c_6463,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_6456])).

cnf(c_742,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1560,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2478,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2535,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2534])).

cnf(c_3105,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3087])).

cnf(c_6464,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_6456])).

cnf(c_6482,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6464])).

cnf(c_745,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1721,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_2583,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_4247,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_relat_1(sK4),sK1)
    | k1_relat_1(sK4) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_6529,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(sK1,sK1)
    | k1_relat_1(sK4) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4247])).

cnf(c_6593,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6463,c_1560,c_2478,c_2535,c_3105,c_3158,c_6482,c_6529])).

cnf(c_6594,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6593])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6606,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6594,c_28])).

cnf(c_2735,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1288])).

cnf(c_5547,plain,
    ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_2735])).

cnf(c_6183,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3087,c_5547])).

cnf(c_6215,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6183,c_2534])).

cnf(c_6650,plain,
    ( k2_relset_1(k1_relat_1(sK4),k1_xboole_0,sK4) = k2_relat_1(sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6606,c_6215])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1727,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1729,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | sK4 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2546,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_21,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_156])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1282,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1413,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1282,c_8])).

cnf(c_75,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_77,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_80,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_1805,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1413,c_77,c_82])).

cnf(c_1806,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1805])).

cnf(c_6655,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6606,c_1806])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1524,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_1903,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_1905,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_1652,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2126,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1584,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5132,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_1507,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_6104,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_6097])).

cnf(c_6699,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6655])).

cnf(c_6829,plain,
    ( sK4 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6655,c_1906,c_2126,c_5135,c_6105])).

cnf(c_6830,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6829])).

cnf(c_6654,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6606,c_3087])).

cnf(c_2639,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1291])).

cnf(c_4701,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2639])).

cnf(c_4783,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_4701])).

cnf(c_7279,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6654,c_4783])).

cnf(c_7374,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ v1_relat_1(sK4)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7279])).

cnf(c_7469,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6650,c_1729,c_2535,c_2546,c_6830,c_7374])).

cnf(c_7495,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7469,c_2306])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7538,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7495,c_9])).

cnf(c_1293,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1295,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3374,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_1295])).

cnf(c_7789,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7538,c_3374])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_156])).

cnf(c_441,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1280,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_1404,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1280,c_9])).

cnf(c_7498,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7469,c_1404])).

cnf(c_7529,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7498])).

cnf(c_7503,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7469,c_1285])).

cnf(c_7506,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7503,c_9])).

cnf(c_7533,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7529,c_7506])).

cnf(c_7534,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7533,c_9])).

cnf(c_1728,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1727])).

cnf(c_1730,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_1904,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | sK4 != X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_1906,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_2250,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2251,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(c_2253,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_2549,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2546])).

cnf(c_5135,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5132])).

cnf(c_6103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6097])).

cnf(c_6105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6103])).

cnf(c_8190,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7534,c_1404,c_1729,c_1730,c_1906,c_2126,c_2253,c_2535,c_2546,c_2549,c_5135,c_6105,c_6830,c_7374,c_7506])).

cnf(c_8483,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7789,c_8190])).

cnf(c_2932,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1289])).

cnf(c_3495,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_2932])).

cnf(c_4092,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1294,c_3495])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4094,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4092,c_17])).

cnf(c_8504,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8483,c_4094])).

cnf(c_8505,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8504])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.00  
% 3.33/1.00  ------  iProver source info
% 3.33/1.00  
% 3.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.00  git: non_committed_changes: false
% 3.33/1.00  git: last_make_outside_of_git: false
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     num_symb
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       true
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  ------ Parsing...
% 3.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.00  ------ Proving...
% 3.33/1.00  ------ Problem Properties 
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  clauses                                 28
% 3.33/1.00  conjectures                             3
% 3.33/1.00  EPR                                     8
% 3.33/1.00  Horn                                    25
% 3.33/1.00  unary                                   10
% 3.33/1.00  binary                                  8
% 3.33/1.00  lits                                    61
% 3.33/1.00  lits eq                                 28
% 3.33/1.00  fd_pure                                 0
% 3.33/1.00  fd_pseudo                               0
% 3.33/1.00  fd_cond                                 2
% 3.33/1.00  fd_pseudo_cond                          1
% 3.33/1.00  AC symbols                              0
% 3.33/1.00  
% 3.33/1.00  ------ Schedule dynamic 5 is on 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  Current options:
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     none
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       false
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00   Resolution empty clause
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f7,axiom,(
% 3.33/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f37,plain,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.33/1.00    inference(nnf_transformation,[],[f7])).
% 3.33/1.00  
% 3.33/1.00  fof(f53,plain,(
% 3.33/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f4,axiom,(
% 3.33/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f4])).
% 3.33/1.00  
% 3.33/1.00  fof(f34,plain,(
% 3.33/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.00    inference(flattening,[],[f33])).
% 3.33/1.00  
% 3.33/1.00  fof(f45,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.33/1.00    inference(cnf_transformation,[],[f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f75,plain,(
% 3.33/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/1.00    inference(equality_resolution,[],[f45])).
% 3.33/1.00  
% 3.33/1.00  fof(f16,conjecture,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f17,negated_conjecture,(
% 3.33/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.33/1.00    inference(negated_conjecture,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.33/1.00    inference(ennf_transformation,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.33/1.00    inference(flattening,[],[f27])).
% 3.33/1.00  
% 3.33/1.00  fof(f39,plain,(
% 3.33/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f40,plain,(
% 3.33/1.00    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39])).
% 3.33/1.00  
% 3.33/1.00  fof(f70,plain,(
% 3.33/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f13,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f22,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f60,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f71,plain,(
% 3.33/1.00    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f15,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f25,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f26,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f25])).
% 3.33/1.00  
% 3.33/1.00  fof(f38,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(nnf_transformation,[],[f26])).
% 3.33/1.00  
% 3.33/1.00  fof(f62,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f69,plain,(
% 3.33/1.00    v1_funct_2(sK4,sK1,sK2)),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f12,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f21,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f12])).
% 3.33/1.00  
% 3.33/1.00  fof(f59,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f21])).
% 3.33/1.00  
% 3.33/1.00  fof(f14,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(ennf_transformation,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(flattening,[],[f23])).
% 3.33/1.00  
% 3.33/1.00  fof(f61,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f52,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f20,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f55,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,axiom,(
% 3.33/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f64,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f68,plain,(
% 3.33/1.00    v1_funct_1(sK4)),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f72,plain,(
% 3.33/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f47,plain,(
% 3.33/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f5,axiom,(
% 3.33/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f48,plain,(
% 3.33/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f5])).
% 3.33/1.00  
% 3.33/1.00  fof(f67,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f78,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(equality_resolution,[],[f67])).
% 3.33/1.00  
% 3.33/1.00  fof(f79,plain,(
% 3.33/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.33/1.00    inference(equality_resolution,[],[f78])).
% 3.33/1.00  
% 3.33/1.00  fof(f6,axiom,(
% 3.33/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f35,plain,(
% 3.33/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.33/1.00    inference(nnf_transformation,[],[f6])).
% 3.33/1.00  
% 3.33/1.00  fof(f36,plain,(
% 3.33/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.33/1.00    inference(flattening,[],[f35])).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.33/1.00    inference(cnf_transformation,[],[f36])).
% 3.33/1.00  
% 3.33/1.00  fof(f76,plain,(
% 3.33/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.33/1.00    inference(equality_resolution,[],[f51])).
% 3.33/1.00  
% 3.33/1.00  fof(f50,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.33/1.00    inference(cnf_transformation,[],[f36])).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.33/1.00    inference(equality_resolution,[],[f50])).
% 3.33/1.00  
% 3.33/1.00  fof(f65,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f81,plain,(
% 3.33/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.33/1.00    inference(equality_resolution,[],[f65])).
% 3.33/1.00  
% 3.33/1.00  fof(f11,axiom,(
% 3.33/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f57,plain,(
% 3.33/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.33/1.00    inference(cnf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_11,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1292,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.33/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f75]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1294,plain,
% 3.33/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_30,negated_conjecture,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1285,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_19,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1288,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2736,plain,
% 3.33/1.00      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1285,c_1288]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_29,negated_conjecture,
% 3.33/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1286,plain,
% 3.33/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3087,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_2736,c_1286]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_26,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.33/1.00      | k1_xboole_0 = X2 ),
% 3.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_31,negated_conjecture,
% 3.33/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_482,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.33/1.00      | sK2 != X2
% 3.33/1.00      | sK1 != X1
% 3.33/1.00      | sK4 != X0
% 3.33/1.00      | k1_xboole_0 = X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_483,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.33/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.33/1.00      | k1_xboole_0 = sK2 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_485,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_483,c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_18,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1289,plain,
% 3.33/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2930,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1285,c_1289]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3158,plain,
% 3.33/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_485,c_2930]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_20,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.33/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1287,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.33/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2929,plain,
% 3.33/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.33/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1287,c_1289]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5969,plain,
% 3.33/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.33/1.00      | r1_tarski(sK1,X0) != iProver_top
% 3.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3158,c_2929]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_12,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1291,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2306,plain,
% 3.33/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1285,c_1291]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_14,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_217,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.33/1.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_218,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_217]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_276,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.33/1.00      inference(bin_hyper_res,[status(thm)],[c_14,c_218]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1284,plain,
% 3.33/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2310,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.33/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_2306,c_1284]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_15,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1290,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2534,plain,
% 3.33/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2310,c_1290]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6330,plain,
% 3.33/1.00      ( r1_tarski(sK1,X0) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4) ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5969,c_2534]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6331,plain,
% 3.33/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.33/1.00      | r1_tarski(sK1,X0) != iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_6330]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6342,plain,
% 3.33/1.00      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | r1_tarski(sK1,X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3087,c_6331]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6380,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) | sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1294,c_6342]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_24,plain,
% 3.33/1.00      ( v1_funct_2(X0,X1,X2)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.33/1.00      | k1_xboole_0 = X2 ),
% 3.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_27,negated_conjecture,
% 3.33/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ v1_funct_1(sK4) ),
% 3.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_32,negated_conjecture,
% 3.33/1.00      ( v1_funct_1(sK4) ),
% 3.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_155,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_27,c_32]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_156,negated_conjecture,
% 3.33/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_155]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_469,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.33/1.00      | sK3 != X2
% 3.33/1.00      | sK1 != X1
% 3.33/1.00      | sK4 != X0
% 3.33/1.00      | k1_xboole_0 = X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_156]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_470,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.33/1.00      | k1_xboole_0 = sK3 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_469]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1278,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.33/1.00      | k1_xboole_0 = sK3
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6453,plain,
% 3.33/1.00      ( k1_relat_1(sK4) != sK1
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | sK3 = k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6380,c_1278]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6456,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0
% 3.33/1.00      | sK3 = k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6453,c_3158]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6463,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0
% 3.33/1.00      | sK3 = k1_xboole_0
% 3.33/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1292,c_6456]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_742,plain,( X0 = X0 ),theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1560,plain,
% 3.33/1.00      ( sK1 = sK1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_742]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2478,plain,
% 3.33/1.00      ( r1_tarski(sK1,sK1) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2535,plain,
% 3.33/1.00      ( v1_relat_1(sK4) ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2534]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3105,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3087]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6464,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0
% 3.33/1.00      | sK3 = k1_xboole_0
% 3.33/1.00      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1287,c_6456]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6482,plain,
% 3.33/1.00      ( ~ r1_tarski(k1_relat_1(sK4),sK1)
% 3.33/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.33/1.00      | ~ v1_relat_1(sK4)
% 3.33/1.00      | sK2 = k1_xboole_0
% 3.33/1.00      | sK3 = k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6464]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_745,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.33/1.00      theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1721,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_745]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2583,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1721]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4247,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,sK1)
% 3.33/1.00      | r1_tarski(k1_relat_1(sK4),sK1)
% 3.33/1.00      | k1_relat_1(sK4) != X0
% 3.33/1.00      | sK1 != sK1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2583]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6529,plain,
% 3.33/1.00      ( r1_tarski(k1_relat_1(sK4),sK1)
% 3.33/1.00      | ~ r1_tarski(sK1,sK1)
% 3.33/1.00      | k1_relat_1(sK4) != sK1
% 3.33/1.00      | sK1 != sK1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_4247]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6593,plain,
% 3.33/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_6463,c_1560,c_2478,c_2535,c_3105,c_3158,c_6482,c_6529]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6594,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_6593]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_28,negated_conjecture,
% 3.33/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6606,plain,
% 3.33/1.00      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6594,c_28]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2735,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1287,c_1288]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5547,plain,
% 3.33/1.00      ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1294,c_2735]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6183,plain,
% 3.33/1.00      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
% 3.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3087,c_5547]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6215,plain,
% 3.33/1.00      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4) ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6183,c_2534]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6650,plain,
% 3.33/1.00      ( k2_relset_1(k1_relat_1(sK4),k1_xboole_0,sK4) = k2_relat_1(sK4)
% 3.33/1.00      | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6606,c_6215]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1727,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1729,plain,
% 3.33/1.00      ( ~ r1_tarski(sK4,k1_xboole_0)
% 3.33/1.00      | ~ r1_tarski(k1_xboole_0,sK4)
% 3.33/1.00      | sK4 = k1_xboole_0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1727]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2546,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_21,plain,
% 3.33/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_397,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.33/1.00      | sK3 != k1_xboole_0
% 3.33/1.00      | sK1 != X0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_156]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_398,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.33/1.00      | sK3 != k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = sK1 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1282,plain,
% 3.33/1.00      ( sK3 != k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 = sK1
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8,plain,
% 3.33/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1413,plain,
% 3.33/1.00      ( sK3 != k1_xboole_0
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_1282,c_8]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_75,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.33/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_77,plain,
% 3.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.33/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_75]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_80,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_82,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_80]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1805,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | sK3 != k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_1413,c_77,c_82]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1806,plain,
% 3.33/1.00      ( sK3 != k1_xboole_0
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_1805]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6655,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6606,c_1806]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_748,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.33/1.00      theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1524,plain,
% 3.33/1.00      ( m1_subset_1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.33/1.00      | X0 != X2
% 3.33/1.00      | X1 != k1_zfmisc_1(X3) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_748]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1651,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.33/1.00      | X2 != X0
% 3.33/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1524]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1903,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 3.33/1.00      | sK4 != X0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1651]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1905,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 3.33/1.00      | sK4 != k1_xboole_0 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1903]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1652,plain,
% 3.33/1.00      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_742]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2126,plain,
% 3.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1652]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1584,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5132,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1584]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1507,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6097,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK3)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1507]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6104,plain,
% 3.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_6097]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6699,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | sK4 != k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6655]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6829,plain,
% 3.33/1.00      ( sK4 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_6655,c_1906,c_2126,c_5135,c_6105]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6830,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_6829]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6654,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6606,c_3087]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2639,plain,
% 3.33/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 3.33/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1287,c_1291]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4701,plain,
% 3.33/1.00      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.33/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_8,c_2639]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4783,plain,
% 3.33/1.00      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1294,c_4701]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7279,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0
% 3.33/1.00      | r1_tarski(sK4,k1_xboole_0) = iProver_top
% 3.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_6654,c_4783]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7374,plain,
% 3.33/1.00      ( r1_tarski(sK4,k1_xboole_0) | ~ v1_relat_1(sK4) | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7279]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7469,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_6650,c_1729,c_2535,c_2546,c_6830,c_7374]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7495,plain,
% 3.33/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7469,c_2306]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9,plain,
% 3.33/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7538,plain,
% 3.33/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7495,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1293,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1295,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.33/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3374,plain,
% 3.33/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1293,c_1295]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7789,plain,
% 3.33/1.00      ( sK4 = k1_xboole_0 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7538,c_3374]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_23,plain,
% 3.33/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_440,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.33/1.00      | sK3 != X1
% 3.33/1.00      | sK1 != k1_xboole_0
% 3.33/1.00      | sK4 != X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_156]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_441,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.33/1.00      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | sK1 != k1_xboole_0 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_440]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1280,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | sK1 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1404,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | sK1 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_1280,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7498,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | k1_xboole_0 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7469,c_1404]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7529,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_7498]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7503,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7469,c_1285]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7506,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7503,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7533,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7529,c_7506]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7534,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7533,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1728,plain,
% 3.33/1.00      ( sK4 = X0
% 3.33/1.00      | r1_tarski(X0,sK4) != iProver_top
% 3.33/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1727]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1730,plain,
% 3.33/1.00      ( sK4 = k1_xboole_0
% 3.33/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.33/1.00      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1728]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1904,plain,
% 3.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 3.33/1.00      | sK4 != X0
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1906,plain,
% 3.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 3.33/1.00      | sK4 != k1_xboole_0
% 3.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.33/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1904]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2250,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2251,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.33/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2250]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2253,plain,
% 3.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.33/1.00      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2251]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2549,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2546]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5135,plain,
% 3.33/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_5132]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6103,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.33/1.00      | r1_tarski(X0,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6097]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6105,plain,
% 3.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.33/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_6103]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8190,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_7534,c_1404,c_1729,c_1730,c_1906,c_2126,c_2253,c_2535,
% 3.33/1.00                 c_2546,c_2549,c_5135,c_6105,c_6830,c_7374,c_7506]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8483,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_7789,c_8190]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2932,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.33/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_9,c_1289]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3495,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.33/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1292,c_2932]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4092,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1294,c_3495]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_17,plain,
% 3.33/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4094,plain,
% 3.33/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_4092,c_17]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8504,plain,
% 3.33/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8483,c_4094]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8505,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_8504]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ General
% 3.33/1.00  
% 3.33/1.00  abstr_ref_over_cycles:                  0
% 3.33/1.00  abstr_ref_under_cycles:                 0
% 3.33/1.00  gc_basic_clause_elim:                   0
% 3.33/1.00  forced_gc_time:                         0
% 3.33/1.00  parsing_time:                           0.028
% 3.33/1.00  unif_index_cands_time:                  0.
% 3.33/1.00  unif_index_add_time:                    0.
% 3.33/1.00  orderings_time:                         0.
% 3.33/1.00  out_proof_time:                         0.012
% 3.33/1.00  total_time:                             0.248
% 3.33/1.00  num_of_symbols:                         50
% 3.33/1.00  num_of_terms:                           5582
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing
% 3.33/1.00  
% 3.33/1.00  num_of_splits:                          0
% 3.33/1.00  num_of_split_atoms:                     0
% 3.33/1.00  num_of_reused_defs:                     0
% 3.33/1.00  num_eq_ax_congr_red:                    4
% 3.33/1.00  num_of_sem_filtered_clauses:            2
% 3.33/1.00  num_of_subtypes:                        0
% 3.33/1.00  monotx_restored_types:                  0
% 3.33/1.00  sat_num_of_epr_types:                   0
% 3.33/1.00  sat_num_of_non_cyclic_types:            0
% 3.33/1.00  sat_guarded_non_collapsed_types:        0
% 3.33/1.00  num_pure_diseq_elim:                    0
% 3.33/1.00  simp_replaced_by:                       0
% 3.33/1.00  res_preprocessed:                       141
% 3.33/1.00  prep_upred:                             0
% 3.33/1.00  prep_unflattend:                        37
% 3.33/1.00  smt_new_axioms:                         0
% 3.33/1.00  pred_elim_cands:                        4
% 3.33/1.00  pred_elim:                              2
% 3.33/1.00  pred_elim_cl:                           3
% 3.33/1.00  pred_elim_cycles:                       4
% 3.33/1.00  merged_defs:                            8
% 3.33/1.00  merged_defs_ncl:                        0
% 3.33/1.00  bin_hyper_res:                          10
% 3.33/1.00  prep_cycles:                            4
% 3.33/1.00  pred_elim_time:                         0.005
% 3.33/1.00  splitting_time:                         0.
% 3.33/1.00  sem_filter_time:                        0.
% 3.33/1.00  monotx_time:                            0.
% 3.33/1.00  subtype_inf_time:                       0.
% 3.33/1.00  
% 3.33/1.00  ------ Problem properties
% 3.33/1.00  
% 3.33/1.00  clauses:                                28
% 3.33/1.00  conjectures:                            3
% 3.33/1.00  epr:                                    8
% 3.33/1.00  horn:                                   25
% 3.33/1.00  ground:                                 13
% 3.33/1.00  unary:                                  10
% 3.33/1.00  binary:                                 8
% 3.33/1.00  lits:                                   61
% 3.33/1.00  lits_eq:                                28
% 3.33/1.00  fd_pure:                                0
% 3.33/1.00  fd_pseudo:                              0
% 3.33/1.00  fd_cond:                                2
% 3.33/1.00  fd_pseudo_cond:                         1
% 3.33/1.00  ac_symbols:                             0
% 3.33/1.00  
% 3.33/1.00  ------ Propositional Solver
% 3.33/1.00  
% 3.33/1.00  prop_solver_calls:                      30
% 3.33/1.00  prop_fast_solver_calls:                 1046
% 3.33/1.00  smt_solver_calls:                       0
% 3.33/1.00  smt_fast_solver_calls:                  0
% 3.33/1.00  prop_num_of_clauses:                    2851
% 3.33/1.00  prop_preprocess_simplified:             6659
% 3.33/1.00  prop_fo_subsumed:                       40
% 3.33/1.00  prop_solver_time:                       0.
% 3.33/1.00  smt_solver_time:                        0.
% 3.33/1.00  smt_fast_solver_time:                   0.
% 3.33/1.00  prop_fast_solver_time:                  0.
% 3.33/1.00  prop_unsat_core_time:                   0.
% 3.33/1.00  
% 3.33/1.00  ------ QBF
% 3.33/1.00  
% 3.33/1.00  qbf_q_res:                              0
% 3.33/1.00  qbf_num_tautologies:                    0
% 3.33/1.00  qbf_prep_cycles:                        0
% 3.33/1.00  
% 3.33/1.00  ------ BMC1
% 3.33/1.00  
% 3.33/1.00  bmc1_current_bound:                     -1
% 3.33/1.00  bmc1_last_solved_bound:                 -1
% 3.33/1.00  bmc1_unsat_core_size:                   -1
% 3.33/1.00  bmc1_unsat_core_parents_size:           -1
% 3.33/1.00  bmc1_merge_next_fun:                    0
% 3.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation
% 3.33/1.00  
% 3.33/1.00  inst_num_of_clauses:                    933
% 3.33/1.00  inst_num_in_passive:                    222
% 3.33/1.00  inst_num_in_active:                     483
% 3.33/1.00  inst_num_in_unprocessed:                229
% 3.33/1.00  inst_num_of_loops:                      590
% 3.33/1.00  inst_num_of_learning_restarts:          0
% 3.33/1.00  inst_num_moves_active_passive:          103
% 3.33/1.00  inst_lit_activity:                      0
% 3.33/1.00  inst_lit_activity_moves:                0
% 3.33/1.00  inst_num_tautologies:                   0
% 3.33/1.00  inst_num_prop_implied:                  0
% 3.33/1.00  inst_num_existing_simplified:           0
% 3.33/1.00  inst_num_eq_res_simplified:             0
% 3.33/1.00  inst_num_child_elim:                    0
% 3.33/1.00  inst_num_of_dismatching_blockings:      330
% 3.33/1.00  inst_num_of_non_proper_insts:           1243
% 3.33/1.00  inst_num_of_duplicates:                 0
% 3.33/1.00  inst_inst_num_from_inst_to_res:         0
% 3.33/1.00  inst_dismatching_checking_time:         0.
% 3.33/1.00  
% 3.33/1.00  ------ Resolution
% 3.33/1.00  
% 3.33/1.00  res_num_of_clauses:                     0
% 3.33/1.00  res_num_in_passive:                     0
% 3.33/1.00  res_num_in_active:                      0
% 3.33/1.00  res_num_of_loops:                       145
% 3.33/1.00  res_forward_subset_subsumed:            65
% 3.33/1.00  res_backward_subset_subsumed:           4
% 3.33/1.00  res_forward_subsumed:                   0
% 3.33/1.00  res_backward_subsumed:                  0
% 3.33/1.00  res_forward_subsumption_resolution:     0
% 3.33/1.00  res_backward_subsumption_resolution:    0
% 3.33/1.00  res_clause_to_clause_subsumption:       819
% 3.33/1.00  res_orphan_elimination:                 0
% 3.33/1.00  res_tautology_del:                      115
% 3.33/1.00  res_num_eq_res_simplified:              1
% 3.33/1.00  res_num_sel_changes:                    0
% 3.33/1.00  res_moves_from_active_to_pass:          0
% 3.33/1.00  
% 3.33/1.00  ------ Superposition
% 3.33/1.00  
% 3.33/1.00  sup_time_total:                         0.
% 3.33/1.00  sup_time_generating:                    0.
% 3.33/1.00  sup_time_sim_full:                      0.
% 3.33/1.00  sup_time_sim_immed:                     0.
% 3.33/1.00  
% 3.33/1.00  sup_num_of_clauses:                     105
% 3.33/1.00  sup_num_in_active:                      53
% 3.33/1.00  sup_num_in_passive:                     52
% 3.33/1.00  sup_num_of_loops:                       116
% 3.33/1.00  sup_fw_superposition:                   115
% 3.33/1.00  sup_bw_superposition:                   103
% 3.33/1.00  sup_immediate_simplified:               78
% 3.33/1.00  sup_given_eliminated:                   3
% 3.33/1.00  comparisons_done:                       0
% 3.33/1.00  comparisons_avoided:                    42
% 3.33/1.00  
% 3.33/1.00  ------ Simplifications
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  sim_fw_subset_subsumed:                 26
% 3.33/1.00  sim_bw_subset_subsumed:                 25
% 3.33/1.00  sim_fw_subsumed:                        14
% 3.33/1.00  sim_bw_subsumed:                        7
% 3.33/1.00  sim_fw_subsumption_res:                 3
% 3.33/1.00  sim_bw_subsumption_res:                 0
% 3.33/1.00  sim_tautology_del:                      10
% 3.33/1.00  sim_eq_tautology_del:                   16
% 3.33/1.00  sim_eq_res_simp:                        2
% 3.33/1.00  sim_fw_demodulated:                     22
% 3.33/1.00  sim_bw_demodulated:                     56
% 3.33/1.00  sim_light_normalised:                   32
% 3.33/1.00  sim_joinable_taut:                      0
% 3.33/1.00  sim_joinable_simp:                      0
% 3.33/1.00  sim_ac_normalised:                      0
% 3.33/1.00  sim_smt_subsumption:                    0
% 3.33/1.00  
%------------------------------------------------------------------------------
