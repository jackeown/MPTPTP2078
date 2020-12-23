%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:31 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  239 (2983 expanded)
%              Number of clauses        :  171 (1144 expanded)
%              Number of leaves         :   17 ( 535 expanded)
%              Depth                    :   24
%              Number of atoms          :  740 (14490 expanded)
%              Number of equality atoms :  455 (4672 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,
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

fof(f34,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_461,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_25])).

cnf(c_1141,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1145,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2478,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1141,c_1145])).

cnf(c_2649,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_461,c_2478])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_329,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_11])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_1140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_1487,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1140])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1144,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2288,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1141,c_1144])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1142,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2491,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2288,c_1142])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2477,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1145])).

cnf(c_10720,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2477])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1274,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_1275,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_11067,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10720,c_30,c_1275])).

cnf(c_11068,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11067])).

cnf(c_11076,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1487,c_11068])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_141,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_27])).

cnf(c_142,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_142])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1135,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_11174,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11076,c_1135])).

cnf(c_1191,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1192,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_11177,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11174,c_30,c_1192,c_1275,c_1487,c_2491])).

cnf(c_11178,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11177])).

cnf(c_11179,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2649,c_11178])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11289,plain,
    ( sK2 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11179,c_23])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_78,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_79,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1236,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1238,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1447,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_373,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK0 != X0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_142])).

cnf(c_374,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1139,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1155,plain,
    ( sK2 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1139,c_4])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_75,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_77,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_80,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_1681,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_77,c_82])).

cnf(c_1682,plain,
    ( sK2 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1681])).

cnf(c_2492,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2491])).

cnf(c_710,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2531,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2532,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_709,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2550,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_3435,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1924,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1143])).

cnf(c_3378,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1924])).

cnf(c_3455,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3378,c_30,c_1275])).

cnf(c_3456,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3455])).

cnf(c_3457,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3456])).

cnf(c_711,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1517,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1895,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1)
    | X1 != X0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_5056,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | X0 != sK2
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_5058,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5056])).

cnf(c_11296,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11289,c_30,c_78,c_79,c_1192,c_1238,c_1275,c_1449,c_1487,c_1682,c_2491,c_2492,c_2532,c_2550,c_3435,c_3457,c_5058])).

cnf(c_11299,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11296,c_11076])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_142])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1137,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1154,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1137,c_5])).

cnf(c_11387,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11296,c_1154])).

cnf(c_11396,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11387])).

cnf(c_11397,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11396,c_5])).

cnf(c_11442,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11299,c_11397])).

cnf(c_11381,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11296,c_2478])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_433,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1136,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_1152,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1136,c_5])).

cnf(c_11388,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11296,c_1152])).

cnf(c_11395,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11388])).

cnf(c_11399,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11381,c_11395])).

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1926,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1147])).

cnf(c_1151,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3859,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_1151])).

cnf(c_7626,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | r1_tarski(k1_relat_1(X1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_3859])).

cnf(c_7627,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7626,c_5])).

cnf(c_7711,plain,
    ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7627,c_80])).

cnf(c_7712,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7711])).

cnf(c_7724,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2649,c_7712])).

cnf(c_1237,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_1239,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1322,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_1138,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1153,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1138,c_4])).

cnf(c_1185,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1234,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1313,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_1415,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1416,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1686,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_23,c_78,c_79,c_1234,c_1313,c_1416])).

cnf(c_1771,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1147])).

cnf(c_1772,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1771])).

cnf(c_2261,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2262,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_1455,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1882,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_2873,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_2875,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_3436,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3435])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1150,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1925,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1143])).

cnf(c_3449,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2649,c_1925])).

cnf(c_3579,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3449,c_30,c_1275])).

cnf(c_3580,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3579])).

cnf(c_3585,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_3580])).

cnf(c_3654,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3585,c_1147])).

cnf(c_712,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_4145,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_4146,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4145])).

cnf(c_3350,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_6922,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_3350])).

cnf(c_6923,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6922])).

cnf(c_7875,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7724,c_78,c_79,c_1238,c_1239,c_1322,c_1686,c_1772,c_2262,c_2875,c_3435,c_3436,c_3654,c_4146,c_6923])).

cnf(c_7876,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7875])).

cnf(c_7877,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7876])).

cnf(c_1669,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1670,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1672,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_1456,plain,
    ( X0 != X1
    | sK3 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_1458,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_1208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1210,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11442,c_11399,c_11296,c_7877,c_1672,c_1458,c_1210,c_82,c_81,c_79,c_78])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:27:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.67/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.97  
% 3.67/0.97  ------  iProver source info
% 3.67/0.97  
% 3.67/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.97  git: non_committed_changes: false
% 3.67/0.97  git: last_make_outside_of_git: false
% 3.67/0.97  
% 3.67/0.97  ------ 
% 3.67/0.97  
% 3.67/0.97  ------ Input Options
% 3.67/0.97  
% 3.67/0.97  --out_options                           all
% 3.67/0.97  --tptp_safe_out                         true
% 3.67/0.97  --problem_path                          ""
% 3.67/0.97  --include_path                          ""
% 3.67/0.97  --clausifier                            res/vclausify_rel
% 3.67/0.97  --clausifier_options                    ""
% 3.67/0.97  --stdin                                 false
% 3.67/0.97  --stats_out                             all
% 3.67/0.97  
% 3.67/0.97  ------ General Options
% 3.67/0.97  
% 3.67/0.97  --fof                                   false
% 3.67/0.97  --time_out_real                         305.
% 3.67/0.97  --time_out_virtual                      -1.
% 3.67/0.97  --symbol_type_check                     false
% 3.67/0.97  --clausify_out                          false
% 3.67/0.97  --sig_cnt_out                           false
% 3.67/0.97  --trig_cnt_out                          false
% 3.67/0.97  --trig_cnt_out_tolerance                1.
% 3.67/0.97  --trig_cnt_out_sk_spl                   false
% 3.67/0.97  --abstr_cl_out                          false
% 3.67/0.97  
% 3.67/0.97  ------ Global Options
% 3.67/0.97  
% 3.67/0.97  --schedule                              default
% 3.67/0.97  --add_important_lit                     false
% 3.67/0.97  --prop_solver_per_cl                    1000
% 3.67/0.97  --min_unsat_core                        false
% 3.67/0.97  --soft_assumptions                      false
% 3.67/0.97  --soft_lemma_size                       3
% 3.67/0.97  --prop_impl_unit_size                   0
% 3.67/0.97  --prop_impl_unit                        []
% 3.67/0.97  --share_sel_clauses                     true
% 3.67/0.97  --reset_solvers                         false
% 3.67/0.97  --bc_imp_inh                            [conj_cone]
% 3.67/0.97  --conj_cone_tolerance                   3.
% 3.67/0.97  --extra_neg_conj                        none
% 3.67/0.97  --large_theory_mode                     true
% 3.67/0.97  --prolific_symb_bound                   200
% 3.67/0.97  --lt_threshold                          2000
% 3.67/0.97  --clause_weak_htbl                      true
% 3.67/0.97  --gc_record_bc_elim                     false
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing Options
% 3.67/0.97  
% 3.67/0.97  --preprocessing_flag                    true
% 3.67/0.97  --time_out_prep_mult                    0.1
% 3.67/0.97  --splitting_mode                        input
% 3.67/0.97  --splitting_grd                         true
% 3.67/0.97  --splitting_cvd                         false
% 3.67/0.97  --splitting_cvd_svl                     false
% 3.67/0.97  --splitting_nvd                         32
% 3.67/0.97  --sub_typing                            true
% 3.67/0.97  --prep_gs_sim                           true
% 3.67/0.97  --prep_unflatten                        true
% 3.67/0.97  --prep_res_sim                          true
% 3.67/0.97  --prep_upred                            true
% 3.67/0.97  --prep_sem_filter                       exhaustive
% 3.67/0.97  --prep_sem_filter_out                   false
% 3.67/0.97  --pred_elim                             true
% 3.67/0.97  --res_sim_input                         true
% 3.67/0.97  --eq_ax_congr_red                       true
% 3.67/0.97  --pure_diseq_elim                       true
% 3.67/0.97  --brand_transform                       false
% 3.67/0.97  --non_eq_to_eq                          false
% 3.67/0.97  --prep_def_merge                        true
% 3.67/0.97  --prep_def_merge_prop_impl              false
% 3.67/0.97  --prep_def_merge_mbd                    true
% 3.67/0.97  --prep_def_merge_tr_red                 false
% 3.67/0.97  --prep_def_merge_tr_cl                  false
% 3.67/0.97  --smt_preprocessing                     true
% 3.67/0.97  --smt_ac_axioms                         fast
% 3.67/0.97  --preprocessed_out                      false
% 3.67/0.97  --preprocessed_stats                    false
% 3.67/0.97  
% 3.67/0.97  ------ Abstraction refinement Options
% 3.67/0.97  
% 3.67/0.97  --abstr_ref                             []
% 3.67/0.97  --abstr_ref_prep                        false
% 3.67/0.97  --abstr_ref_until_sat                   false
% 3.67/0.97  --abstr_ref_sig_restrict                funpre
% 3.67/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.97  --abstr_ref_under                       []
% 3.67/0.97  
% 3.67/0.97  ------ SAT Options
% 3.67/0.97  
% 3.67/0.97  --sat_mode                              false
% 3.67/0.97  --sat_fm_restart_options                ""
% 3.67/0.97  --sat_gr_def                            false
% 3.67/0.97  --sat_epr_types                         true
% 3.67/0.97  --sat_non_cyclic_types                  false
% 3.67/0.97  --sat_finite_models                     false
% 3.67/0.97  --sat_fm_lemmas                         false
% 3.67/0.97  --sat_fm_prep                           false
% 3.67/0.97  --sat_fm_uc_incr                        true
% 3.67/0.97  --sat_out_model                         small
% 3.67/0.97  --sat_out_clauses                       false
% 3.67/0.97  
% 3.67/0.97  ------ QBF Options
% 3.67/0.97  
% 3.67/0.97  --qbf_mode                              false
% 3.67/0.97  --qbf_elim_univ                         false
% 3.67/0.97  --qbf_dom_inst                          none
% 3.67/0.97  --qbf_dom_pre_inst                      false
% 3.67/0.97  --qbf_sk_in                             false
% 3.67/0.97  --qbf_pred_elim                         true
% 3.67/0.97  --qbf_split                             512
% 3.67/0.97  
% 3.67/0.97  ------ BMC1 Options
% 3.67/0.97  
% 3.67/0.97  --bmc1_incremental                      false
% 3.67/0.97  --bmc1_axioms                           reachable_all
% 3.67/0.97  --bmc1_min_bound                        0
% 3.67/0.97  --bmc1_max_bound                        -1
% 3.67/0.97  --bmc1_max_bound_default                -1
% 3.67/0.97  --bmc1_symbol_reachability              true
% 3.67/0.97  --bmc1_property_lemmas                  false
% 3.67/0.97  --bmc1_k_induction                      false
% 3.67/0.97  --bmc1_non_equiv_states                 false
% 3.67/0.97  --bmc1_deadlock                         false
% 3.67/0.97  --bmc1_ucm                              false
% 3.67/0.97  --bmc1_add_unsat_core                   none
% 3.67/0.97  --bmc1_unsat_core_children              false
% 3.67/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.97  --bmc1_out_stat                         full
% 3.67/0.97  --bmc1_ground_init                      false
% 3.67/0.97  --bmc1_pre_inst_next_state              false
% 3.67/0.97  --bmc1_pre_inst_state                   false
% 3.67/0.97  --bmc1_pre_inst_reach_state             false
% 3.67/0.97  --bmc1_out_unsat_core                   false
% 3.67/0.97  --bmc1_aig_witness_out                  false
% 3.67/0.97  --bmc1_verbose                          false
% 3.67/0.97  --bmc1_dump_clauses_tptp                false
% 3.67/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.97  --bmc1_dump_file                        -
% 3.67/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.97  --bmc1_ucm_extend_mode                  1
% 3.67/0.97  --bmc1_ucm_init_mode                    2
% 3.67/0.97  --bmc1_ucm_cone_mode                    none
% 3.67/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.97  --bmc1_ucm_relax_model                  4
% 3.67/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.97  --bmc1_ucm_layered_model                none
% 3.67/0.97  --bmc1_ucm_max_lemma_size               10
% 3.67/0.97  
% 3.67/0.97  ------ AIG Options
% 3.67/0.97  
% 3.67/0.97  --aig_mode                              false
% 3.67/0.97  
% 3.67/0.97  ------ Instantiation Options
% 3.67/0.97  
% 3.67/0.97  --instantiation_flag                    true
% 3.67/0.97  --inst_sos_flag                         true
% 3.67/0.97  --inst_sos_phase                        true
% 3.67/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.97  --inst_lit_sel_side                     num_symb
% 3.67/0.97  --inst_solver_per_active                1400
% 3.67/0.97  --inst_solver_calls_frac                1.
% 3.67/0.97  --inst_passive_queue_type               priority_queues
% 3.67/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.97  --inst_passive_queues_freq              [25;2]
% 3.67/0.97  --inst_dismatching                      true
% 3.67/0.97  --inst_eager_unprocessed_to_passive     true
% 3.67/0.97  --inst_prop_sim_given                   true
% 3.67/0.97  --inst_prop_sim_new                     false
% 3.67/0.97  --inst_subs_new                         false
% 3.67/0.97  --inst_eq_res_simp                      false
% 3.67/0.97  --inst_subs_given                       false
% 3.67/0.97  --inst_orphan_elimination               true
% 3.67/0.97  --inst_learning_loop_flag               true
% 3.67/0.97  --inst_learning_start                   3000
% 3.67/0.97  --inst_learning_factor                  2
% 3.67/0.97  --inst_start_prop_sim_after_learn       3
% 3.67/0.97  --inst_sel_renew                        solver
% 3.67/0.97  --inst_lit_activity_flag                true
% 3.67/0.97  --inst_restr_to_given                   false
% 3.67/0.97  --inst_activity_threshold               500
% 3.67/0.97  --inst_out_proof                        true
% 3.67/0.97  
% 3.67/0.97  ------ Resolution Options
% 3.67/0.97  
% 3.67/0.97  --resolution_flag                       true
% 3.67/0.97  --res_lit_sel                           adaptive
% 3.67/0.97  --res_lit_sel_side                      none
% 3.67/0.97  --res_ordering                          kbo
% 3.67/0.97  --res_to_prop_solver                    active
% 3.67/0.97  --res_prop_simpl_new                    false
% 3.67/0.97  --res_prop_simpl_given                  true
% 3.67/0.97  --res_passive_queue_type                priority_queues
% 3.67/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.97  --res_passive_queues_freq               [15;5]
% 3.67/0.97  --res_forward_subs                      full
% 3.67/0.97  --res_backward_subs                     full
% 3.67/0.97  --res_forward_subs_resolution           true
% 3.67/0.97  --res_backward_subs_resolution          true
% 3.67/0.97  --res_orphan_elimination                true
% 3.67/0.97  --res_time_limit                        2.
% 3.67/0.97  --res_out_proof                         true
% 3.67/0.97  
% 3.67/0.97  ------ Superposition Options
% 3.67/0.97  
% 3.67/0.97  --superposition_flag                    true
% 3.67/0.97  --sup_passive_queue_type                priority_queues
% 3.67/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.97  --demod_completeness_check              fast
% 3.67/0.97  --demod_use_ground                      true
% 3.67/0.97  --sup_to_prop_solver                    passive
% 3.67/0.97  --sup_prop_simpl_new                    true
% 3.67/0.97  --sup_prop_simpl_given                  true
% 3.67/0.97  --sup_fun_splitting                     true
% 3.67/0.97  --sup_smt_interval                      50000
% 3.67/0.97  
% 3.67/0.97  ------ Superposition Simplification Setup
% 3.67/0.97  
% 3.67/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.97  --sup_immed_triv                        [TrivRules]
% 3.67/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_immed_bw_main                     []
% 3.67/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_input_bw                          []
% 3.67/0.97  
% 3.67/0.97  ------ Combination Options
% 3.67/0.97  
% 3.67/0.97  --comb_res_mult                         3
% 3.67/0.97  --comb_sup_mult                         2
% 3.67/0.97  --comb_inst_mult                        10
% 3.67/0.97  
% 3.67/0.97  ------ Debug Options
% 3.67/0.97  
% 3.67/0.97  --dbg_backtrace                         false
% 3.67/0.97  --dbg_dump_prop_clauses                 false
% 3.67/0.97  --dbg_dump_prop_clauses_file            -
% 3.67/0.97  --dbg_out_stat                          false
% 3.67/0.97  ------ Parsing...
% 3.67/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  ------ Proving...
% 3.67/0.97  ------ Problem Properties 
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  clauses                                 23
% 3.67/0.97  conjectures                             3
% 3.67/0.97  EPR                                     4
% 3.67/0.97  Horn                                    20
% 3.67/0.97  unary                                   6
% 3.67/0.97  binary                                  9
% 3.67/0.97  lits                                    53
% 3.67/0.97  lits eq                                 25
% 3.67/0.97  fd_pure                                 0
% 3.67/0.97  fd_pseudo                               0
% 3.67/0.97  fd_cond                                 1
% 3.67/0.97  fd_pseudo_cond                          1
% 3.67/0.97  AC symbols                              0
% 3.67/0.97  
% 3.67/0.97  ------ Schedule dynamic 5 is on 
% 3.67/0.97  
% 3.67/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ 
% 3.67/0.97  Current options:
% 3.67/0.97  ------ 
% 3.67/0.97  
% 3.67/0.97  ------ Input Options
% 3.67/0.97  
% 3.67/0.97  --out_options                           all
% 3.67/0.97  --tptp_safe_out                         true
% 3.67/0.97  --problem_path                          ""
% 3.67/0.97  --include_path                          ""
% 3.67/0.97  --clausifier                            res/vclausify_rel
% 3.67/0.97  --clausifier_options                    ""
% 3.67/0.97  --stdin                                 false
% 3.67/0.97  --stats_out                             all
% 3.67/0.97  
% 3.67/0.97  ------ General Options
% 3.67/0.97  
% 3.67/0.97  --fof                                   false
% 3.67/0.97  --time_out_real                         305.
% 3.67/0.97  --time_out_virtual                      -1.
% 3.67/0.97  --symbol_type_check                     false
% 3.67/0.97  --clausify_out                          false
% 3.67/0.97  --sig_cnt_out                           false
% 3.67/0.97  --trig_cnt_out                          false
% 3.67/0.97  --trig_cnt_out_tolerance                1.
% 3.67/0.97  --trig_cnt_out_sk_spl                   false
% 3.67/0.97  --abstr_cl_out                          false
% 3.67/0.97  
% 3.67/0.97  ------ Global Options
% 3.67/0.97  
% 3.67/0.97  --schedule                              default
% 3.67/0.97  --add_important_lit                     false
% 3.67/0.97  --prop_solver_per_cl                    1000
% 3.67/0.97  --min_unsat_core                        false
% 3.67/0.97  --soft_assumptions                      false
% 3.67/0.97  --soft_lemma_size                       3
% 3.67/0.97  --prop_impl_unit_size                   0
% 3.67/0.97  --prop_impl_unit                        []
% 3.67/0.97  --share_sel_clauses                     true
% 3.67/0.97  --reset_solvers                         false
% 3.67/0.97  --bc_imp_inh                            [conj_cone]
% 3.67/0.97  --conj_cone_tolerance                   3.
% 3.67/0.97  --extra_neg_conj                        none
% 3.67/0.97  --large_theory_mode                     true
% 3.67/0.97  --prolific_symb_bound                   200
% 3.67/0.97  --lt_threshold                          2000
% 3.67/0.97  --clause_weak_htbl                      true
% 3.67/0.97  --gc_record_bc_elim                     false
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing Options
% 3.67/0.97  
% 3.67/0.97  --preprocessing_flag                    true
% 3.67/0.97  --time_out_prep_mult                    0.1
% 3.67/0.97  --splitting_mode                        input
% 3.67/0.97  --splitting_grd                         true
% 3.67/0.97  --splitting_cvd                         false
% 3.67/0.97  --splitting_cvd_svl                     false
% 3.67/0.97  --splitting_nvd                         32
% 3.67/0.97  --sub_typing                            true
% 3.67/0.97  --prep_gs_sim                           true
% 3.67/0.97  --prep_unflatten                        true
% 3.67/0.97  --prep_res_sim                          true
% 3.67/0.97  --prep_upred                            true
% 3.67/0.97  --prep_sem_filter                       exhaustive
% 3.67/0.97  --prep_sem_filter_out                   false
% 3.67/0.97  --pred_elim                             true
% 3.67/0.97  --res_sim_input                         true
% 3.67/0.97  --eq_ax_congr_red                       true
% 3.67/0.97  --pure_diseq_elim                       true
% 3.67/0.97  --brand_transform                       false
% 3.67/0.97  --non_eq_to_eq                          false
% 3.67/0.97  --prep_def_merge                        true
% 3.67/0.97  --prep_def_merge_prop_impl              false
% 3.67/0.97  --prep_def_merge_mbd                    true
% 3.67/0.97  --prep_def_merge_tr_red                 false
% 3.67/0.97  --prep_def_merge_tr_cl                  false
% 3.67/0.97  --smt_preprocessing                     true
% 3.67/0.97  --smt_ac_axioms                         fast
% 3.67/0.97  --preprocessed_out                      false
% 3.67/0.97  --preprocessed_stats                    false
% 3.67/0.97  
% 3.67/0.97  ------ Abstraction refinement Options
% 3.67/0.97  
% 3.67/0.97  --abstr_ref                             []
% 3.67/0.97  --abstr_ref_prep                        false
% 3.67/0.97  --abstr_ref_until_sat                   false
% 3.67/0.97  --abstr_ref_sig_restrict                funpre
% 3.67/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.97  --abstr_ref_under                       []
% 3.67/0.97  
% 3.67/0.97  ------ SAT Options
% 3.67/0.97  
% 3.67/0.97  --sat_mode                              false
% 3.67/0.97  --sat_fm_restart_options                ""
% 3.67/0.97  --sat_gr_def                            false
% 3.67/0.97  --sat_epr_types                         true
% 3.67/0.97  --sat_non_cyclic_types                  false
% 3.67/0.97  --sat_finite_models                     false
% 3.67/0.97  --sat_fm_lemmas                         false
% 3.67/0.97  --sat_fm_prep                           false
% 3.67/0.97  --sat_fm_uc_incr                        true
% 3.67/0.97  --sat_out_model                         small
% 3.67/0.97  --sat_out_clauses                       false
% 3.67/0.97  
% 3.67/0.97  ------ QBF Options
% 3.67/0.97  
% 3.67/0.97  --qbf_mode                              false
% 3.67/0.97  --qbf_elim_univ                         false
% 3.67/0.97  --qbf_dom_inst                          none
% 3.67/0.97  --qbf_dom_pre_inst                      false
% 3.67/0.97  --qbf_sk_in                             false
% 3.67/0.97  --qbf_pred_elim                         true
% 3.67/0.97  --qbf_split                             512
% 3.67/0.97  
% 3.67/0.97  ------ BMC1 Options
% 3.67/0.97  
% 3.67/0.97  --bmc1_incremental                      false
% 3.67/0.97  --bmc1_axioms                           reachable_all
% 3.67/0.97  --bmc1_min_bound                        0
% 3.67/0.97  --bmc1_max_bound                        -1
% 3.67/0.97  --bmc1_max_bound_default                -1
% 3.67/0.97  --bmc1_symbol_reachability              true
% 3.67/0.97  --bmc1_property_lemmas                  false
% 3.67/0.97  --bmc1_k_induction                      false
% 3.67/0.97  --bmc1_non_equiv_states                 false
% 3.67/0.97  --bmc1_deadlock                         false
% 3.67/0.97  --bmc1_ucm                              false
% 3.67/0.97  --bmc1_add_unsat_core                   none
% 3.67/0.97  --bmc1_unsat_core_children              false
% 3.67/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.97  --bmc1_out_stat                         full
% 3.67/0.97  --bmc1_ground_init                      false
% 3.67/0.97  --bmc1_pre_inst_next_state              false
% 3.67/0.97  --bmc1_pre_inst_state                   false
% 3.67/0.97  --bmc1_pre_inst_reach_state             false
% 3.67/0.97  --bmc1_out_unsat_core                   false
% 3.67/0.97  --bmc1_aig_witness_out                  false
% 3.67/0.97  --bmc1_verbose                          false
% 3.67/0.97  --bmc1_dump_clauses_tptp                false
% 3.67/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.97  --bmc1_dump_file                        -
% 3.67/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.97  --bmc1_ucm_extend_mode                  1
% 3.67/0.97  --bmc1_ucm_init_mode                    2
% 3.67/0.97  --bmc1_ucm_cone_mode                    none
% 3.67/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.97  --bmc1_ucm_relax_model                  4
% 3.67/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.97  --bmc1_ucm_layered_model                none
% 3.67/0.97  --bmc1_ucm_max_lemma_size               10
% 3.67/0.97  
% 3.67/0.97  ------ AIG Options
% 3.67/0.97  
% 3.67/0.97  --aig_mode                              false
% 3.67/0.97  
% 3.67/0.97  ------ Instantiation Options
% 3.67/0.97  
% 3.67/0.97  --instantiation_flag                    true
% 3.67/0.97  --inst_sos_flag                         true
% 3.67/0.97  --inst_sos_phase                        true
% 3.67/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.97  --inst_lit_sel_side                     none
% 3.67/0.97  --inst_solver_per_active                1400
% 3.67/0.97  --inst_solver_calls_frac                1.
% 3.67/0.97  --inst_passive_queue_type               priority_queues
% 3.67/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.97  --inst_passive_queues_freq              [25;2]
% 3.67/0.97  --inst_dismatching                      true
% 3.67/0.97  --inst_eager_unprocessed_to_passive     true
% 3.67/0.97  --inst_prop_sim_given                   true
% 3.67/0.97  --inst_prop_sim_new                     false
% 3.67/0.97  --inst_subs_new                         false
% 3.67/0.97  --inst_eq_res_simp                      false
% 3.67/0.97  --inst_subs_given                       false
% 3.67/0.97  --inst_orphan_elimination               true
% 3.67/0.97  --inst_learning_loop_flag               true
% 3.67/0.97  --inst_learning_start                   3000
% 3.67/0.97  --inst_learning_factor                  2
% 3.67/0.97  --inst_start_prop_sim_after_learn       3
% 3.67/0.97  --inst_sel_renew                        solver
% 3.67/0.97  --inst_lit_activity_flag                true
% 3.67/0.97  --inst_restr_to_given                   false
% 3.67/0.97  --inst_activity_threshold               500
% 3.67/0.97  --inst_out_proof                        true
% 3.67/0.97  
% 3.67/0.97  ------ Resolution Options
% 3.67/0.97  
% 3.67/0.97  --resolution_flag                       false
% 3.67/0.97  --res_lit_sel                           adaptive
% 3.67/0.97  --res_lit_sel_side                      none
% 3.67/0.97  --res_ordering                          kbo
% 3.67/0.97  --res_to_prop_solver                    active
% 3.67/0.97  --res_prop_simpl_new                    false
% 3.67/0.97  --res_prop_simpl_given                  true
% 3.67/0.97  --res_passive_queue_type                priority_queues
% 3.67/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.97  --res_passive_queues_freq               [15;5]
% 3.67/0.97  --res_forward_subs                      full
% 3.67/0.97  --res_backward_subs                     full
% 3.67/0.97  --res_forward_subs_resolution           true
% 3.67/0.97  --res_backward_subs_resolution          true
% 3.67/0.97  --res_orphan_elimination                true
% 3.67/0.97  --res_time_limit                        2.
% 3.67/0.97  --res_out_proof                         true
% 3.67/0.97  
% 3.67/0.97  ------ Superposition Options
% 3.67/0.97  
% 3.67/0.97  --superposition_flag                    true
% 3.67/0.97  --sup_passive_queue_type                priority_queues
% 3.67/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.97  --demod_completeness_check              fast
% 3.67/0.97  --demod_use_ground                      true
% 3.67/0.97  --sup_to_prop_solver                    passive
% 3.67/0.97  --sup_prop_simpl_new                    true
% 3.67/0.97  --sup_prop_simpl_given                  true
% 3.67/0.97  --sup_fun_splitting                     true
% 3.67/0.97  --sup_smt_interval                      50000
% 3.67/0.97  
% 3.67/0.97  ------ Superposition Simplification Setup
% 3.67/0.97  
% 3.67/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.97  --sup_immed_triv                        [TrivRules]
% 3.67/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_immed_bw_main                     []
% 3.67/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.97  --sup_input_bw                          []
% 3.67/0.97  
% 3.67/0.97  ------ Combination Options
% 3.67/0.97  
% 3.67/0.97  --comb_res_mult                         3
% 3.67/0.97  --comb_sup_mult                         2
% 3.67/0.97  --comb_inst_mult                        10
% 3.67/0.97  
% 3.67/0.97  ------ Debug Options
% 3.67/0.97  
% 3.67/0.97  --dbg_backtrace                         false
% 3.67/0.97  --dbg_dump_prop_clauses                 false
% 3.67/0.97  --dbg_dump_prop_clauses_file            -
% 3.67/0.97  --dbg_out_stat                          false
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  % SZS status Theorem for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  fof(f11,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f22,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(ennf_transformation,[],[f11])).
% 3.67/0.97  
% 3.67/0.97  fof(f23,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(flattening,[],[f22])).
% 3.67/0.97  
% 3.67/0.97  fof(f32,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(nnf_transformation,[],[f23])).
% 3.67/0.97  
% 3.67/0.97  fof(f51,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f12,conjecture,(
% 3.67/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f13,negated_conjecture,(
% 3.67/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.67/0.97    inference(negated_conjecture,[],[f12])).
% 3.67/0.97  
% 3.67/0.97  fof(f24,plain,(
% 3.67/0.97    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.67/0.97    inference(ennf_transformation,[],[f13])).
% 3.67/0.97  
% 3.67/0.97  fof(f25,plain,(
% 3.67/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.67/0.97    inference(flattening,[],[f24])).
% 3.67/0.97  
% 3.67/0.97  fof(f33,plain,(
% 3.67/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.67/0.97    introduced(choice_axiom,[])).
% 3.67/0.97  
% 3.67/0.97  fof(f34,plain,(
% 3.67/0.97    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.67/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33])).
% 3.67/0.97  
% 3.67/0.97  fof(f58,plain,(
% 3.67/0.97    v1_funct_2(sK3,sK0,sK1)),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f59,plain,(
% 3.67/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f8,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f18,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(ennf_transformation,[],[f8])).
% 3.67/0.97  
% 3.67/0.97  fof(f48,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f18])).
% 3.67/0.97  
% 3.67/0.97  fof(f7,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f14,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.67/0.97    inference(pure_predicate_removal,[],[f7])).
% 3.67/0.97  
% 3.67/0.97  fof(f17,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(ennf_transformation,[],[f14])).
% 3.67/0.97  
% 3.67/0.97  fof(f47,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f17])).
% 3.67/0.97  
% 3.67/0.97  fof(f5,axiom,(
% 3.67/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f15,plain,(
% 3.67/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.67/0.97    inference(ennf_transformation,[],[f5])).
% 3.67/0.97  
% 3.67/0.97  fof(f31,plain,(
% 3.67/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.67/0.97    inference(nnf_transformation,[],[f15])).
% 3.67/0.97  
% 3.67/0.97  fof(f44,plain,(
% 3.67/0.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f31])).
% 3.67/0.97  
% 3.67/0.97  fof(f6,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f16,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(ennf_transformation,[],[f6])).
% 3.67/0.97  
% 3.67/0.97  fof(f46,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f16])).
% 3.67/0.97  
% 3.67/0.97  fof(f9,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f19,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.97    inference(ennf_transformation,[],[f9])).
% 3.67/0.97  
% 3.67/0.97  fof(f49,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f19])).
% 3.67/0.97  
% 3.67/0.97  fof(f60,plain,(
% 3.67/0.97    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f10,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f20,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.67/0.97    inference(ennf_transformation,[],[f10])).
% 3.67/0.97  
% 3.67/0.97  fof(f21,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.67/0.97    inference(flattening,[],[f20])).
% 3.67/0.97  
% 3.67/0.97  fof(f50,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f21])).
% 3.67/0.97  
% 3.67/0.97  fof(f53,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f62,plain,(
% 3.67/0.97    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f57,plain,(
% 3.67/0.97    v1_funct_1(sK3)),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f61,plain,(
% 3.67/0.97    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.67/0.97    inference(cnf_transformation,[],[f34])).
% 3.67/0.97  
% 3.67/0.97  fof(f3,axiom,(
% 3.67/0.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f28,plain,(
% 3.67/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.67/0.97    inference(nnf_transformation,[],[f3])).
% 3.67/0.97  
% 3.67/0.97  fof(f29,plain,(
% 3.67/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.67/0.97    inference(flattening,[],[f28])).
% 3.67/0.97  
% 3.67/0.97  fof(f39,plain,(
% 3.67/0.97    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f40,plain,(
% 3.67/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f66,plain,(
% 3.67/0.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.67/0.97    inference(equality_resolution,[],[f40])).
% 3.67/0.97  
% 3.67/0.97  fof(f1,axiom,(
% 3.67/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f26,plain,(
% 3.67/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.97    inference(nnf_transformation,[],[f1])).
% 3.67/0.97  
% 3.67/0.97  fof(f27,plain,(
% 3.67/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.97    inference(flattening,[],[f26])).
% 3.67/0.97  
% 3.67/0.97  fof(f37,plain,(
% 3.67/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f27])).
% 3.67/0.97  
% 3.67/0.97  fof(f4,axiom,(
% 3.67/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f30,plain,(
% 3.67/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.67/0.97    inference(nnf_transformation,[],[f4])).
% 3.67/0.97  
% 3.67/0.97  fof(f42,plain,(
% 3.67/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f30])).
% 3.67/0.97  
% 3.67/0.97  fof(f56,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f67,plain,(
% 3.67/0.97    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(equality_resolution,[],[f56])).
% 3.67/0.97  
% 3.67/0.97  fof(f68,plain,(
% 3.67/0.97    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.67/0.97    inference(equality_resolution,[],[f67])).
% 3.67/0.97  
% 3.67/0.97  fof(f41,plain,(
% 3.67/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f65,plain,(
% 3.67/0.97    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.67/0.97    inference(equality_resolution,[],[f41])).
% 3.67/0.97  
% 3.67/0.97  fof(f43,plain,(
% 3.67/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f30])).
% 3.67/0.97  
% 3.67/0.97  fof(f2,axiom,(
% 3.67/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f38,plain,(
% 3.67/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f2])).
% 3.67/0.97  
% 3.67/0.97  fof(f54,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f70,plain,(
% 3.67/0.97    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.67/0.97    inference(equality_resolution,[],[f54])).
% 3.67/0.97  
% 3.67/0.97  fof(f52,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f71,plain,(
% 3.67/0.97    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.67/0.97    inference(equality_resolution,[],[f52])).
% 3.67/0.97  
% 3.67/0.97  fof(f55,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f32])).
% 3.67/0.97  
% 3.67/0.97  fof(f69,plain,(
% 3.67/0.97    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.67/0.97    inference(equality_resolution,[],[f55])).
% 3.67/0.97  
% 3.67/0.97  fof(f35,plain,(
% 3.67/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.67/0.97    inference(cnf_transformation,[],[f27])).
% 3.67/0.97  
% 3.67/0.97  fof(f64,plain,(
% 3.67/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.67/0.97    inference(equality_resolution,[],[f35])).
% 3.67/0.97  
% 3.67/0.97  cnf(c_21,plain,
% 3.67/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.67/0.97      | k1_xboole_0 = X2 ),
% 3.67/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_26,negated_conjecture,
% 3.67/0.97      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.67/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_458,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.67/0.97      | sK1 != X2
% 3.67/0.97      | sK0 != X1
% 3.67/0.97      | sK3 != X0
% 3.67/0.97      | k1_xboole_0 = X2 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_459,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/0.97      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.67/0.97      | k1_xboole_0 = sK1 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_458]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_25,negated_conjecture,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.67/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_461,plain,
% 3.67/0.97      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_459,c_25]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1141,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_13,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1145,plain,
% 3.67/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.67/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2478,plain,
% 3.67/0.97      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1141,c_1145]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2649,plain,
% 3.67/0.97      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_461,c_2478]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_12,plain,
% 3.67/0.97      ( v4_relat_1(X0,X1)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.67/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_10,plain,
% 3.67/0.97      ( ~ v4_relat_1(X0,X1)
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.67/0.97      | ~ v1_relat_1(X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_325,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 3.67/0.97      | ~ v1_relat_1(X0) ),
% 3.67/0.97      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | v1_relat_1(X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_329,plain,
% 3.67/0.97      ( r1_tarski(k1_relat_1(X0),X1)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_325,c_11]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_330,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_329]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1140,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1487,plain,
% 3.67/0.97      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1141,c_1140]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_14,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1144,plain,
% 3.67/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.67/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2288,plain,
% 3.67/0.97      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1141,c_1144]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_24,negated_conjecture,
% 3.67/0.97      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 3.67/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1142,plain,
% 3.67/0.97      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2491,plain,
% 3.67/0.97      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_2288,c_1142]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_15,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.67/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.67/0.97      | ~ v1_relat_1(X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1143,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2477,plain,
% 3.67/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.67/0.97      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.67/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1143,c_1145]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_10720,plain,
% 3.67/0.97      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.67/0.97      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2491,c_2477]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_30,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1221,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.97      | v1_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1274,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/0.97      | v1_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1221]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1275,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11067,plain,
% 3.67/0.97      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_10720,c_30,c_1275]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11068,plain,
% 3.67/0.97      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.67/0.97      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_11067]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11076,plain,
% 3.67/0.97      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1487,c_11068]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_19,plain,
% 3.67/0.97      ( v1_funct_2(X0,X1,X2)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | k1_relset_1(X1,X2,X0) != X1
% 3.67/0.97      | k1_xboole_0 = X2 ),
% 3.67/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_22,negated_conjecture,
% 3.67/0.97      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.67/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ v1_funct_1(sK3) ),
% 3.67/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_27,negated_conjecture,
% 3.67/0.97      ( v1_funct_1(sK3) ),
% 3.67/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_141,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_22,c_27]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_142,negated_conjecture,
% 3.67/0.97      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.67/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_141]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_445,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | k1_relset_1(X1,X2,X0) != X1
% 3.67/0.97      | sK2 != X2
% 3.67/0.97      | sK0 != X1
% 3.67/0.97      | sK3 != X0
% 3.67/0.97      | k1_xboole_0 = X2 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_142]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_446,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | k1_relset_1(sK0,sK2,sK3) != sK0
% 3.67/0.97      | k1_xboole_0 = sK2 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_445]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1135,plain,
% 3.67/0.97      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 3.67/0.97      | k1_xboole_0 = sK2
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11174,plain,
% 3.67/0.97      ( k1_relat_1(sK3) != sK0
% 3.67/0.97      | sK2 = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11076,c_1135]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1191,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.67/0.97      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.67/0.97      | ~ v1_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1192,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11177,plain,
% 3.67/0.97      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) != sK0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_11174,c_30,c_1192,c_1275,c_1487,c_2491]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11178,plain,
% 3.67/0.97      ( k1_relat_1(sK3) != sK0 | sK2 = k1_xboole_0 ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_11177]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11179,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2649,c_11178]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_23,negated_conjecture,
% 3.67/0.97      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11289,plain,
% 3.67/0.97      ( sK2 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_11179,c_23]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_6,plain,
% 3.67/0.97      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = X1
% 3.67/0.97      | k1_xboole_0 = X0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_78,plain,
% 3.67/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_5,plain,
% 3.67/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_79,plain,
% 3.67/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_0,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.67/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1236,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1238,plain,
% 3.67/0.97      ( ~ r1_tarski(sK3,k1_xboole_0)
% 3.67/0.97      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.67/0.97      | sK3 = k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1236]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_8,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.67/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1447,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1449,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1447]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_16,plain,
% 3.67/0.97      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.67/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.67/0.97      | k1_xboole_0 = X0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_373,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.67/0.97      | sK2 != k1_xboole_0
% 3.67/0.97      | sK0 != X0
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = X0 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_142]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_374,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.67/0.97      | sK2 != k1_xboole_0
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK0 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_373]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1139,plain,
% 3.67/0.97      ( sK2 != k1_xboole_0
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_4,plain,
% 3.67/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1155,plain,
% 3.67/0.97      ( sK2 != k1_xboole_0
% 3.67/0.97      | sK0 = k1_xboole_0
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_1139,c_4]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.67/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_75,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.67/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_77,plain,
% 3.67/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_75]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_80,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_82,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_80]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1681,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | sK0 = k1_xboole_0
% 3.67/0.97      | sK2 != k1_xboole_0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_1155,c_77,c_82]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1682,plain,
% 3.67/0.97      ( sK2 != k1_xboole_0
% 3.67/0.97      | sK0 = k1_xboole_0
% 3.67/0.97      | sK3 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_1681]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2492,plain,
% 3.67/0.97      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 3.67/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2491]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_710,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2531,plain,
% 3.67/0.97      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_710]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2532,plain,
% 3.67/0.97      ( sK2 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK2
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_2531]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_709,plain,( X0 = X0 ),theory(equality) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2550,plain,
% 3.67/0.97      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_709]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3435,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1924,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_4,c_1143]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3378,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1487,c_1924]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3455,plain,
% 3.67/0.97      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_3378,c_30,c_1275]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3456,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_3455]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3457,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.67/0.97      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
% 3.67/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_3456]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_711,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.67/0.97      theory(equality) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1517,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,X1)
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X2)
% 3.67/0.97      | X2 != X1
% 3.67/0.97      | k2_relat_1(sK3) != X0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_711]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1895,plain,
% 3.67/0.97      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X1)
% 3.67/0.97      | X1 != X0
% 3.67/0.97      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1517]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_5056,plain,
% 3.67/0.97      ( r1_tarski(k2_relat_1(sK3),X0)
% 3.67/0.97      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.67/0.97      | X0 != sK2
% 3.67/0.97      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1895]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_5058,plain,
% 3.67/0.97      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 3.67/0.97      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.67/0.97      | k1_xboole_0 != sK2 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_5056]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11296,plain,
% 3.67/0.97      ( sK0 = k1_xboole_0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_11289,c_30,c_78,c_79,c_1192,c_1238,c_1275,c_1449,
% 3.67/0.97                 c_1487,c_1682,c_2491,c_2492,c_2532,c_2550,c_3435,c_3457,
% 3.67/0.97                 c_5058]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11299,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11296,c_11076]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_18,plain,
% 3.67/0.97      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_416,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.67/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.67/0.97      | sK2 != X1
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | sK3 != X0 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_142]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_417,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.67/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_416]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1137,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1154,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_1137,c_5]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11387,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11296,c_1154]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11396,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(equality_resolution_simp,[status(thm)],[c_11387]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11397,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11396,c_5]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11442,plain,
% 3.67/0.97      ( k1_relat_1(sK3) != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11299,c_11397]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11381,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11296,c_2478]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_20,plain,
% 3.67/0.97      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_432,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.67/0.97      | sK1 != X1
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | sK3 != X0 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_433,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.67/0.97      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_432]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1136,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1152,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_1136,c_5]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11388,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11296,c_1152]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11395,plain,
% 3.67/0.97      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(equality_resolution_simp,[status(thm)],[c_11388]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11399,plain,
% 3.67/0.97      ( k1_relat_1(sK3) = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_11381,c_11395]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1147,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1926,plain,
% 3.67/0.97      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1143,c_1147]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1151,plain,
% 3.67/0.97      ( X0 = X1
% 3.67/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.67/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3859,plain,
% 3.67/0.97      ( k2_zfmisc_1(X0,X1) = X2
% 3.67/0.97      | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.67/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1926,c_1151]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7626,plain,
% 3.67/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.67/0.97      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X1),k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.67/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_5,c_3859]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7627,plain,
% 3.67/0.97      ( k1_xboole_0 = X0
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_7626,c_5]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7711,plain,
% 3.67/0.97      ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | k1_xboole_0 = X0
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_7627,c_80]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7712,plain,
% 3.67/0.97      ( k1_xboole_0 = X0
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_7711]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7724,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0
% 3.67/0.97      | sK3 = k1_xboole_0
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2649,c_7712]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1237,plain,
% 3.67/0.97      ( sK3 = X0
% 3.67/0.97      | r1_tarski(X0,sK3) != iProver_top
% 3.67/0.97      | r1_tarski(sK3,X0) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1239,plain,
% 3.67/0.97      ( sK3 = k1_xboole_0
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1237]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1322,plain,
% 3.67/0.97      ( sK3 = sK3 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_709]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_17,plain,
% 3.67/0.97      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.67/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.67/0.97      | k1_xboole_0 = X1
% 3.67/0.97      | k1_xboole_0 = X0 ),
% 3.67/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_396,plain,
% 3.67/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.67/0.97      | sK1 != k1_xboole_0
% 3.67/0.97      | sK0 != X1
% 3.67/0.97      | sK3 != X0
% 3.67/0.97      | k1_xboole_0 = X1
% 3.67/0.97      | k1_xboole_0 = X0 ),
% 3.67/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_397,plain,
% 3.67/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.67/0.97      | sK1 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK0
% 3.67/0.97      | k1_xboole_0 = sK3 ),
% 3.67/0.97      inference(unflattening,[status(thm)],[c_396]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1138,plain,
% 3.67/0.97      ( sK1 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK0
% 3.67/0.97      | k1_xboole_0 = sK3
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1153,plain,
% 3.67/0.97      ( sK1 != k1_xboole_0
% 3.67/0.97      | sK0 = k1_xboole_0
% 3.67/0.97      | sK3 = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.67/0.97      inference(demodulation,[status(thm)],[c_1138,c_4]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1185,plain,
% 3.67/0.97      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_710]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1234,plain,
% 3.67/0.97      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1185]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1313,plain,
% 3.67/0.97      ( sK0 = sK0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_709]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1415,plain,
% 3.67/0.97      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_710]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1416,plain,
% 3.67/0.97      ( sK1 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = sK1
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1415]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1686,plain,
% 3.67/0.97      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_1153,c_23,c_78,c_79,c_1234,c_1313,c_1416]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1771,plain,
% 3.67/0.97      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1141,c_1147]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1772,plain,
% 3.67/0.97      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.67/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1771]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2261,plain,
% 3.67/0.97      ( k2_zfmisc_1(X0,X1) != X2
% 3.67/0.97      | k1_xboole_0 != X2
% 3.67/0.97      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_710]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2262,plain,
% 3.67/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_2261]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1455,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_711]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1882,plain,
% 3.67/0.97      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1455]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2873,plain,
% 3.67/0.97      ( r1_tarski(sK3,X0)
% 3.67/0.97      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 3.67/0.97      | X0 != k2_zfmisc_1(sK0,sK1)
% 3.67/0.97      | sK3 != sK3 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1882]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2875,plain,
% 3.67/0.97      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0)
% 3.67/0.97      | sK3 != sK3
% 3.67/0.97      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_2873]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3436,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_3435]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2,plain,
% 3.67/0.97      ( r1_tarski(X0,X0) ),
% 3.67/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1150,plain,
% 3.67/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1925,plain,
% 3.67/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.67/0.97      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.67/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_5,c_1143]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3449,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.67/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2649,c_1925]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3579,plain,
% 3.67/0.97      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | sK1 = k1_xboole_0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_3449,c_30,c_1275]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3580,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_3579]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3585,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0
% 3.67/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_1150,c_3580]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3654,plain,
% 3.67/0.97      ( sK1 = k1_xboole_0
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_3585,c_1147]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_712,plain,
% 3.67/0.97      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.67/0.97      theory(equality) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_4145,plain,
% 3.67/0.97      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
% 3.67/0.97      | sK1 != X1
% 3.67/0.97      | sK0 != X0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_712]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_4146,plain,
% 3.67/0.97      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.67/0.97      | sK1 != k1_xboole_0
% 3.67/0.97      | sK0 != k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_4145]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3350,plain,
% 3.67/0.97      ( X0 != X1
% 3.67/0.97      | X0 = k2_zfmisc_1(sK0,sK1)
% 3.67/0.97      | k2_zfmisc_1(sK0,sK1) != X1 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_710]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_6922,plain,
% 3.67/0.97      ( X0 != k2_zfmisc_1(X1,X2)
% 3.67/0.97      | X0 = k2_zfmisc_1(sK0,sK1)
% 3.67/0.97      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_3350]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_6923,plain,
% 3.67/0.97      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.67/0.97      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 3.67/0.97      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_6922]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7875,plain,
% 3.67/0.97      ( r1_tarski(sK0,k1_xboole_0) != iProver_top | sK3 = k1_xboole_0 ),
% 3.67/0.97      inference(global_propositional_subsumption,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_7724,c_78,c_79,c_1238,c_1239,c_1322,c_1686,c_1772,
% 3.67/0.97                 c_2262,c_2875,c_3435,c_3436,c_3654,c_4146,c_6923]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7876,plain,
% 3.67/0.97      ( sK3 = k1_xboole_0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(renaming,[status(thm)],[c_7875]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7877,plain,
% 3.67/0.97      ( ~ r1_tarski(sK0,k1_xboole_0) | sK3 = k1_xboole_0 ),
% 3.67/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_7876]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1669,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~ r1_tarski(sK3,X0) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1670,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 3.67/0.97      | r1_tarski(sK3,X0) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1672,plain,
% 3.67/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1670]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1456,plain,
% 3.67/0.97      ( X0 != X1
% 3.67/0.97      | sK3 != X2
% 3.67/0.97      | r1_tarski(X2,X1) != iProver_top
% 3.67/0.97      | r1_tarski(sK3,X0) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1458,plain,
% 3.67/0.97      ( sK3 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0
% 3.67/0.97      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.67/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1456]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1208,plain,
% 3.67/0.97      ( ~ r1_tarski(X0,X1)
% 3.67/0.97      | r1_tarski(sK0,k1_xboole_0)
% 3.67/0.97      | sK0 != X0
% 3.67/0.97      | k1_xboole_0 != X1 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_711]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_1210,plain,
% 3.67/0.97      ( r1_tarski(sK0,k1_xboole_0)
% 3.67/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.67/0.97      | sK0 != k1_xboole_0
% 3.67/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_1208]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_81,plain,
% 3.67/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.67/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(contradiction,plain,
% 3.67/0.97      ( $false ),
% 3.67/0.97      inference(minisat,
% 3.67/0.97                [status(thm)],
% 3.67/0.97                [c_11442,c_11399,c_11296,c_7877,c_1672,c_1458,c_1210,
% 3.67/0.97                 c_82,c_81,c_79,c_78]) ).
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  ------                               Statistics
% 3.67/0.97  
% 3.67/0.97  ------ General
% 3.67/0.97  
% 3.67/0.97  abstr_ref_over_cycles:                  0
% 3.67/0.97  abstr_ref_under_cycles:                 0
% 3.67/0.97  gc_basic_clause_elim:                   0
% 3.67/0.97  forced_gc_time:                         0
% 3.67/0.97  parsing_time:                           0.009
% 3.67/0.97  unif_index_cands_time:                  0.
% 3.67/0.97  unif_index_add_time:                    0.
% 3.67/0.97  orderings_time:                         0.
% 3.67/0.97  out_proof_time:                         0.014
% 3.67/0.97  total_time:                             0.342
% 3.67/0.97  num_of_symbols:                         48
% 3.67/0.97  num_of_terms:                           7743
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing
% 3.67/0.97  
% 3.67/0.97  num_of_splits:                          0
% 3.67/0.97  num_of_split_atoms:                     0
% 3.67/0.97  num_of_reused_defs:                     0
% 3.67/0.97  num_eq_ax_congr_red:                    13
% 3.67/0.97  num_of_sem_filtered_clauses:            2
% 3.67/0.97  num_of_subtypes:                        0
% 3.67/0.97  monotx_restored_types:                  0
% 3.67/0.97  sat_num_of_epr_types:                   0
% 3.67/0.97  sat_num_of_non_cyclic_types:            0
% 3.67/0.97  sat_guarded_non_collapsed_types:        0
% 3.67/0.97  num_pure_diseq_elim:                    0
% 3.67/0.97  simp_replaced_by:                       0
% 3.67/0.97  res_preprocessed:                       113
% 3.67/0.97  prep_upred:                             0
% 3.67/0.97  prep_unflattend:                        33
% 3.67/0.97  smt_new_axioms:                         0
% 3.67/0.97  pred_elim_cands:                        3
% 3.67/0.97  pred_elim:                              2
% 3.67/0.97  pred_elim_cl:                           3
% 3.67/0.97  pred_elim_cycles:                       5
% 3.67/0.97  merged_defs:                            8
% 3.67/0.97  merged_defs_ncl:                        0
% 3.67/0.97  bin_hyper_res:                          8
% 3.67/0.97  prep_cycles:                            4
% 3.67/0.97  pred_elim_time:                         0.005
% 3.67/0.97  splitting_time:                         0.
% 3.67/0.97  sem_filter_time:                        0.
% 3.67/0.97  monotx_time:                            0.
% 3.67/0.97  subtype_inf_time:                       0.
% 3.67/0.97  
% 3.67/0.97  ------ Problem properties
% 3.67/0.97  
% 3.67/0.97  clauses:                                23
% 3.67/0.97  conjectures:                            3
% 3.67/0.97  epr:                                    4
% 3.67/0.97  horn:                                   20
% 3.67/0.97  ground:                                 10
% 3.67/0.97  unary:                                  6
% 3.67/0.97  binary:                                 9
% 3.67/0.97  lits:                                   53
% 3.67/0.97  lits_eq:                                25
% 3.67/0.97  fd_pure:                                0
% 3.67/0.97  fd_pseudo:                              0
% 3.67/0.97  fd_cond:                                1
% 3.67/0.97  fd_pseudo_cond:                         1
% 3.67/0.97  ac_symbols:                             0
% 3.67/0.97  
% 3.67/0.97  ------ Propositional Solver
% 3.67/0.97  
% 3.67/0.97  prop_solver_calls:                      32
% 3.67/0.97  prop_fast_solver_calls:                 1143
% 3.67/0.97  smt_solver_calls:                       0
% 3.67/0.97  smt_fast_solver_calls:                  0
% 3.67/0.97  prop_num_of_clauses:                    4917
% 3.67/0.97  prop_preprocess_simplified:             9192
% 3.67/0.97  prop_fo_subsumed:                       27
% 3.67/0.97  prop_solver_time:                       0.
% 3.67/0.97  smt_solver_time:                        0.
% 3.67/0.97  smt_fast_solver_time:                   0.
% 3.67/0.97  prop_fast_solver_time:                  0.
% 3.67/0.97  prop_unsat_core_time:                   0.
% 3.67/0.97  
% 3.67/0.97  ------ QBF
% 3.67/0.97  
% 3.67/0.97  qbf_q_res:                              0
% 3.67/0.97  qbf_num_tautologies:                    0
% 3.67/0.97  qbf_prep_cycles:                        0
% 3.67/0.97  
% 3.67/0.97  ------ BMC1
% 3.67/0.97  
% 3.67/0.97  bmc1_current_bound:                     -1
% 3.67/0.97  bmc1_last_solved_bound:                 -1
% 3.67/0.97  bmc1_unsat_core_size:                   -1
% 3.67/0.97  bmc1_unsat_core_parents_size:           -1
% 3.67/0.97  bmc1_merge_next_fun:                    0
% 3.67/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.67/0.97  
% 3.67/0.97  ------ Instantiation
% 3.67/0.97  
% 3.67/0.97  inst_num_of_clauses:                    1378
% 3.67/0.97  inst_num_in_passive:                    38
% 3.67/0.97  inst_num_in_active:                     743
% 3.67/0.97  inst_num_in_unprocessed:                597
% 3.67/0.97  inst_num_of_loops:                      900
% 3.67/0.97  inst_num_of_learning_restarts:          0
% 3.67/0.97  inst_num_moves_active_passive:          153
% 3.67/0.97  inst_lit_activity:                      0
% 3.67/0.97  inst_lit_activity_moves:                0
% 3.67/0.97  inst_num_tautologies:                   0
% 3.67/0.97  inst_num_prop_implied:                  0
% 3.67/0.97  inst_num_existing_simplified:           0
% 3.67/0.97  inst_num_eq_res_simplified:             0
% 3.67/0.97  inst_num_child_elim:                    0
% 3.67/0.97  inst_num_of_dismatching_blockings:      491
% 3.67/0.97  inst_num_of_non_proper_insts:           2214
% 3.67/0.97  inst_num_of_duplicates:                 0
% 3.67/0.97  inst_inst_num_from_inst_to_res:         0
% 3.67/0.97  inst_dismatching_checking_time:         0.
% 3.67/0.97  
% 3.67/0.97  ------ Resolution
% 3.67/0.97  
% 3.67/0.97  res_num_of_clauses:                     0
% 3.67/0.97  res_num_in_passive:                     0
% 3.67/0.97  res_num_in_active:                      0
% 3.67/0.97  res_num_of_loops:                       117
% 3.67/0.97  res_forward_subset_subsumed:            183
% 3.67/0.97  res_backward_subset_subsumed:           0
% 3.67/0.97  res_forward_subsumed:                   0
% 3.67/0.97  res_backward_subsumed:                  0
% 3.67/0.97  res_forward_subsumption_resolution:     0
% 3.67/0.97  res_backward_subsumption_resolution:    0
% 3.67/0.97  res_clause_to_clause_subsumption:       1739
% 3.67/0.97  res_orphan_elimination:                 0
% 3.67/0.97  res_tautology_del:                      201
% 3.67/0.97  res_num_eq_res_simplified:              1
% 3.67/0.97  res_num_sel_changes:                    0
% 3.67/0.97  res_moves_from_active_to_pass:          0
% 3.67/0.97  
% 3.67/0.97  ------ Superposition
% 3.67/0.97  
% 3.67/0.97  sup_time_total:                         0.
% 3.67/0.97  sup_time_generating:                    0.
% 3.67/0.97  sup_time_sim_full:                      0.
% 3.67/0.97  sup_time_sim_immed:                     0.
% 3.67/0.97  
% 3.67/0.97  sup_num_of_clauses:                     313
% 3.67/0.97  sup_num_in_active:                      75
% 3.67/0.97  sup_num_in_passive:                     238
% 3.67/0.97  sup_num_of_loops:                       179
% 3.67/0.97  sup_fw_superposition:                   416
% 3.67/0.97  sup_bw_superposition:                   211
% 3.67/0.97  sup_immediate_simplified:               188
% 3.67/0.97  sup_given_eliminated:                   1
% 3.67/0.97  comparisons_done:                       0
% 3.67/0.97  comparisons_avoided:                    129
% 3.67/0.97  
% 3.67/0.97  ------ Simplifications
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  sim_fw_subset_subsumed:                 28
% 3.67/0.97  sim_bw_subset_subsumed:                 5
% 3.67/0.97  sim_fw_subsumed:                        63
% 3.67/0.97  sim_bw_subsumed:                        8
% 3.67/0.97  sim_fw_subsumption_res:                 0
% 3.67/0.97  sim_bw_subsumption_res:                 0
% 3.67/0.97  sim_tautology_del:                      7
% 3.67/0.97  sim_eq_tautology_del:                   50
% 3.67/0.97  sim_eq_res_simp:                        2
% 3.67/0.97  sim_fw_demodulated:                     43
% 3.67/0.97  sim_bw_demodulated:                     99
% 3.67/0.97  sim_light_normalised:                   85
% 3.67/0.97  sim_joinable_taut:                      0
% 3.67/0.97  sim_joinable_simp:                      0
% 3.67/0.97  sim_ac_normalised:                      0
% 3.67/0.97  sim_smt_subsumption:                    0
% 3.67/0.97  
%------------------------------------------------------------------------------
