%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:30 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 792 expanded)
%              Number of clauses        :  108 ( 308 expanded)
%              Number of leaves         :   20 ( 149 expanded)
%              Depth                    :   20
%              Number of atoms          :  531 (3975 expanded)
%              Number of equality atoms :  235 (1091 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1546,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_444,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_9])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2772,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_1544])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1549,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2489,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1546,c_1549])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1547,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2589,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2489,c_1547])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2863,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1549])).

cnf(c_6261,plain,
    ( k2_relset_1(X0,sK2,sK3) = k2_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2863])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_91,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_93,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_94,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_96,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_97,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_99,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1776,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_1790,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_504,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_506,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_27])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1550,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2503,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1546,c_1550])).

cnf(c_2627,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_506,c_2503])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1553,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2683,plain,
    ( sK1 = k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_1553])).

cnf(c_943,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1778,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1779,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_1781,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_942,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1792,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1847,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_941,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1848,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_559,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_1540,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_92,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_95,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_98,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_101,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1936,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1937,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_2171,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_25,c_92,c_95,c_98,c_101,c_1937])).

cnf(c_2690,plain,
    ( v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2683,c_93,c_96,c_99,c_1781,c_1847,c_1848,c_2171])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_166,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_29])).

cnf(c_167,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_166])).

cnf(c_17,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_398,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_399,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_417,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X3)
    | X0 != X3
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_399])).

cnf(c_418,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_xboole_0(X0)
    | sK2 != X1
    | sK0 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_167,c_418])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_xboole_0(sK0)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_642])).

cnf(c_1533,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_xboole_0(sK0) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_935,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_642])).

cnf(c_1534,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_1627,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1533,c_1534])).

cnf(c_2867,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1627])).

cnf(c_3298,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_3299,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3298])).

cnf(c_3301,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3299])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1551,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2864,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1551])).

cnf(c_6050,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2864])).

cnf(c_2862,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1550])).

cnf(c_6083,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2862])).

cnf(c_6362,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6083,c_32,c_1776])).

cnf(c_6363,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6362])).

cnf(c_6371,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2772,c_6363])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_167])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1543,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_6579,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6371,c_1543])).

cnf(c_6582,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6579,c_32,c_93,c_96,c_99,c_1776,c_1781,c_1790,c_1847,c_1848,c_2171,c_2589,c_2627,c_2867])).

cnf(c_6589,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_6582])).

cnf(c_6698,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6261,c_32,c_93,c_96,c_99,c_1776,c_1790,c_2589,c_2690,c_2867,c_3301,c_6050,c_6589])).

cnf(c_6706,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2772,c_6698])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.74/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/1.00  
% 2.74/1.00  ------  iProver source info
% 2.74/1.00  
% 2.74/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.74/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/1.00  git: non_committed_changes: false
% 2.74/1.00  git: last_make_outside_of_git: false
% 2.74/1.00  
% 2.74/1.00  ------ 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options
% 2.74/1.00  
% 2.74/1.00  --out_options                           all
% 2.74/1.00  --tptp_safe_out                         true
% 2.74/1.00  --problem_path                          ""
% 2.74/1.00  --include_path                          ""
% 2.74/1.00  --clausifier                            res/vclausify_rel
% 2.74/1.00  --clausifier_options                    --mode clausify
% 2.74/1.00  --stdin                                 false
% 2.74/1.00  --stats_out                             all
% 2.74/1.00  
% 2.74/1.00  ------ General Options
% 2.74/1.00  
% 2.74/1.00  --fof                                   false
% 2.74/1.00  --time_out_real                         305.
% 2.74/1.00  --time_out_virtual                      -1.
% 2.74/1.00  --symbol_type_check                     false
% 2.74/1.00  --clausify_out                          false
% 2.74/1.00  --sig_cnt_out                           false
% 2.74/1.00  --trig_cnt_out                          false
% 2.74/1.00  --trig_cnt_out_tolerance                1.
% 2.74/1.00  --trig_cnt_out_sk_spl                   false
% 2.74/1.00  --abstr_cl_out                          false
% 2.74/1.00  
% 2.74/1.00  ------ Global Options
% 2.74/1.00  
% 2.74/1.00  --schedule                              default
% 2.74/1.00  --add_important_lit                     false
% 2.74/1.00  --prop_solver_per_cl                    1000
% 2.74/1.00  --min_unsat_core                        false
% 2.74/1.00  --soft_assumptions                      false
% 2.74/1.00  --soft_lemma_size                       3
% 2.74/1.00  --prop_impl_unit_size                   0
% 2.74/1.00  --prop_impl_unit                        []
% 2.74/1.00  --share_sel_clauses                     true
% 2.74/1.00  --reset_solvers                         false
% 2.74/1.00  --bc_imp_inh                            [conj_cone]
% 2.74/1.00  --conj_cone_tolerance                   3.
% 2.74/1.00  --extra_neg_conj                        none
% 2.74/1.00  --large_theory_mode                     true
% 2.74/1.00  --prolific_symb_bound                   200
% 2.74/1.00  --lt_threshold                          2000
% 2.74/1.00  --clause_weak_htbl                      true
% 2.74/1.00  --gc_record_bc_elim                     false
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing Options
% 2.74/1.00  
% 2.74/1.00  --preprocessing_flag                    true
% 2.74/1.00  --time_out_prep_mult                    0.1
% 2.74/1.00  --splitting_mode                        input
% 2.74/1.00  --splitting_grd                         true
% 2.74/1.00  --splitting_cvd                         false
% 2.74/1.00  --splitting_cvd_svl                     false
% 2.74/1.00  --splitting_nvd                         32
% 2.74/1.00  --sub_typing                            true
% 2.74/1.00  --prep_gs_sim                           true
% 2.74/1.00  --prep_unflatten                        true
% 2.74/1.00  --prep_res_sim                          true
% 2.74/1.00  --prep_upred                            true
% 2.74/1.00  --prep_sem_filter                       exhaustive
% 2.74/1.00  --prep_sem_filter_out                   false
% 2.74/1.00  --pred_elim                             true
% 2.74/1.00  --res_sim_input                         true
% 2.74/1.00  --eq_ax_congr_red                       true
% 2.74/1.00  --pure_diseq_elim                       true
% 2.74/1.00  --brand_transform                       false
% 2.74/1.00  --non_eq_to_eq                          false
% 2.74/1.00  --prep_def_merge                        true
% 2.74/1.00  --prep_def_merge_prop_impl              false
% 2.74/1.00  --prep_def_merge_mbd                    true
% 2.74/1.00  --prep_def_merge_tr_red                 false
% 2.74/1.00  --prep_def_merge_tr_cl                  false
% 2.74/1.00  --smt_preprocessing                     true
% 2.74/1.00  --smt_ac_axioms                         fast
% 2.74/1.00  --preprocessed_out                      false
% 2.74/1.00  --preprocessed_stats                    false
% 2.74/1.00  
% 2.74/1.00  ------ Abstraction refinement Options
% 2.74/1.00  
% 2.74/1.00  --abstr_ref                             []
% 2.74/1.00  --abstr_ref_prep                        false
% 2.74/1.00  --abstr_ref_until_sat                   false
% 2.74/1.00  --abstr_ref_sig_restrict                funpre
% 2.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.00  --abstr_ref_under                       []
% 2.74/1.00  
% 2.74/1.00  ------ SAT Options
% 2.74/1.00  
% 2.74/1.00  --sat_mode                              false
% 2.74/1.00  --sat_fm_restart_options                ""
% 2.74/1.00  --sat_gr_def                            false
% 2.74/1.00  --sat_epr_types                         true
% 2.74/1.00  --sat_non_cyclic_types                  false
% 2.74/1.00  --sat_finite_models                     false
% 2.74/1.00  --sat_fm_lemmas                         false
% 2.74/1.00  --sat_fm_prep                           false
% 2.74/1.00  --sat_fm_uc_incr                        true
% 2.74/1.00  --sat_out_model                         small
% 2.74/1.00  --sat_out_clauses                       false
% 2.74/1.00  
% 2.74/1.00  ------ QBF Options
% 2.74/1.00  
% 2.74/1.00  --qbf_mode                              false
% 2.74/1.00  --qbf_elim_univ                         false
% 2.74/1.00  --qbf_dom_inst                          none
% 2.74/1.00  --qbf_dom_pre_inst                      false
% 2.74/1.00  --qbf_sk_in                             false
% 2.74/1.00  --qbf_pred_elim                         true
% 2.74/1.00  --qbf_split                             512
% 2.74/1.00  
% 2.74/1.00  ------ BMC1 Options
% 2.74/1.00  
% 2.74/1.00  --bmc1_incremental                      false
% 2.74/1.00  --bmc1_axioms                           reachable_all
% 2.74/1.00  --bmc1_min_bound                        0
% 2.74/1.00  --bmc1_max_bound                        -1
% 2.74/1.00  --bmc1_max_bound_default                -1
% 2.74/1.00  --bmc1_symbol_reachability              true
% 2.74/1.00  --bmc1_property_lemmas                  false
% 2.74/1.00  --bmc1_k_induction                      false
% 2.74/1.00  --bmc1_non_equiv_states                 false
% 2.74/1.00  --bmc1_deadlock                         false
% 2.74/1.00  --bmc1_ucm                              false
% 2.74/1.00  --bmc1_add_unsat_core                   none
% 2.74/1.00  --bmc1_unsat_core_children              false
% 2.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.00  --bmc1_out_stat                         full
% 2.74/1.00  --bmc1_ground_init                      false
% 2.74/1.00  --bmc1_pre_inst_next_state              false
% 2.74/1.00  --bmc1_pre_inst_state                   false
% 2.74/1.00  --bmc1_pre_inst_reach_state             false
% 2.74/1.00  --bmc1_out_unsat_core                   false
% 2.74/1.00  --bmc1_aig_witness_out                  false
% 2.74/1.00  --bmc1_verbose                          false
% 2.74/1.00  --bmc1_dump_clauses_tptp                false
% 2.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.00  --bmc1_dump_file                        -
% 2.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.00  --bmc1_ucm_extend_mode                  1
% 2.74/1.00  --bmc1_ucm_init_mode                    2
% 2.74/1.00  --bmc1_ucm_cone_mode                    none
% 2.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.00  --bmc1_ucm_relax_model                  4
% 2.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.00  --bmc1_ucm_layered_model                none
% 2.74/1.00  --bmc1_ucm_max_lemma_size               10
% 2.74/1.00  
% 2.74/1.00  ------ AIG Options
% 2.74/1.00  
% 2.74/1.00  --aig_mode                              false
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation Options
% 2.74/1.00  
% 2.74/1.00  --instantiation_flag                    true
% 2.74/1.00  --inst_sos_flag                         false
% 2.74/1.00  --inst_sos_phase                        true
% 2.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel_side                     num_symb
% 2.74/1.00  --inst_solver_per_active                1400
% 2.74/1.00  --inst_solver_calls_frac                1.
% 2.74/1.00  --inst_passive_queue_type               priority_queues
% 2.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.00  --inst_passive_queues_freq              [25;2]
% 2.74/1.00  --inst_dismatching                      true
% 2.74/1.00  --inst_eager_unprocessed_to_passive     true
% 2.74/1.00  --inst_prop_sim_given                   true
% 2.74/1.00  --inst_prop_sim_new                     false
% 2.74/1.00  --inst_subs_new                         false
% 2.74/1.00  --inst_eq_res_simp                      false
% 2.74/1.00  --inst_subs_given                       false
% 2.74/1.00  --inst_orphan_elimination               true
% 2.74/1.00  --inst_learning_loop_flag               true
% 2.74/1.00  --inst_learning_start                   3000
% 2.74/1.00  --inst_learning_factor                  2
% 2.74/1.00  --inst_start_prop_sim_after_learn       3
% 2.74/1.00  --inst_sel_renew                        solver
% 2.74/1.00  --inst_lit_activity_flag                true
% 2.74/1.00  --inst_restr_to_given                   false
% 2.74/1.00  --inst_activity_threshold               500
% 2.74/1.00  --inst_out_proof                        true
% 2.74/1.00  
% 2.74/1.00  ------ Resolution Options
% 2.74/1.00  
% 2.74/1.00  --resolution_flag                       true
% 2.74/1.00  --res_lit_sel                           adaptive
% 2.74/1.00  --res_lit_sel_side                      none
% 2.74/1.00  --res_ordering                          kbo
% 2.74/1.00  --res_to_prop_solver                    active
% 2.74/1.00  --res_prop_simpl_new                    false
% 2.74/1.00  --res_prop_simpl_given                  true
% 2.74/1.00  --res_passive_queue_type                priority_queues
% 2.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.00  --res_passive_queues_freq               [15;5]
% 2.74/1.00  --res_forward_subs                      full
% 2.74/1.00  --res_backward_subs                     full
% 2.74/1.00  --res_forward_subs_resolution           true
% 2.74/1.00  --res_backward_subs_resolution          true
% 2.74/1.00  --res_orphan_elimination                true
% 2.74/1.00  --res_time_limit                        2.
% 2.74/1.00  --res_out_proof                         true
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Options
% 2.74/1.00  
% 2.74/1.00  --superposition_flag                    true
% 2.74/1.00  --sup_passive_queue_type                priority_queues
% 2.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.00  --demod_completeness_check              fast
% 2.74/1.00  --demod_use_ground                      true
% 2.74/1.00  --sup_to_prop_solver                    passive
% 2.74/1.00  --sup_prop_simpl_new                    true
% 2.74/1.00  --sup_prop_simpl_given                  true
% 2.74/1.00  --sup_fun_splitting                     false
% 2.74/1.00  --sup_smt_interval                      50000
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Simplification Setup
% 2.74/1.00  
% 2.74/1.00  --sup_indices_passive                   []
% 2.74/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_full_bw                           [BwDemod]
% 2.74/1.00  --sup_immed_triv                        [TrivRules]
% 2.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_immed_bw_main                     []
% 2.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  
% 2.74/1.00  ------ Combination Options
% 2.74/1.00  
% 2.74/1.00  --comb_res_mult                         3
% 2.74/1.00  --comb_sup_mult                         2
% 2.74/1.00  --comb_inst_mult                        10
% 2.74/1.00  
% 2.74/1.00  ------ Debug Options
% 2.74/1.00  
% 2.74/1.00  --dbg_backtrace                         false
% 2.74/1.00  --dbg_dump_prop_clauses                 false
% 2.74/1.00  --dbg_dump_prop_clauses_file            -
% 2.74/1.00  --dbg_out_stat                          false
% 2.74/1.00  ------ Parsing...
% 2.74/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/1.00  ------ Proving...
% 2.74/1.00  ------ Problem Properties 
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  clauses                                 28
% 2.74/1.00  conjectures                             3
% 2.74/1.00  EPR                                     5
% 2.74/1.00  Horn                                    24
% 2.74/1.00  unary                                   3
% 2.74/1.00  binary                                  15
% 2.74/1.00  lits                                    70
% 2.74/1.00  lits eq                                 23
% 2.74/1.00  fd_pure                                 0
% 2.74/1.00  fd_pseudo                               0
% 2.74/1.00  fd_cond                                 1
% 2.74/1.00  fd_pseudo_cond                          0
% 2.74/1.00  AC symbols                              0
% 2.74/1.00  
% 2.74/1.00  ------ Schedule dynamic 5 is on 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  ------ 
% 2.74/1.00  Current options:
% 2.74/1.00  ------ 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options
% 2.74/1.00  
% 2.74/1.00  --out_options                           all
% 2.74/1.00  --tptp_safe_out                         true
% 2.74/1.00  --problem_path                          ""
% 2.74/1.00  --include_path                          ""
% 2.74/1.00  --clausifier                            res/vclausify_rel
% 2.74/1.00  --clausifier_options                    --mode clausify
% 2.74/1.00  --stdin                                 false
% 2.74/1.00  --stats_out                             all
% 2.74/1.00  
% 2.74/1.00  ------ General Options
% 2.74/1.00  
% 2.74/1.00  --fof                                   false
% 2.74/1.00  --time_out_real                         305.
% 2.74/1.00  --time_out_virtual                      -1.
% 2.74/1.00  --symbol_type_check                     false
% 2.74/1.00  --clausify_out                          false
% 2.74/1.00  --sig_cnt_out                           false
% 2.74/1.00  --trig_cnt_out                          false
% 2.74/1.00  --trig_cnt_out_tolerance                1.
% 2.74/1.00  --trig_cnt_out_sk_spl                   false
% 2.74/1.00  --abstr_cl_out                          false
% 2.74/1.00  
% 2.74/1.00  ------ Global Options
% 2.74/1.00  
% 2.74/1.00  --schedule                              default
% 2.74/1.00  --add_important_lit                     false
% 2.74/1.00  --prop_solver_per_cl                    1000
% 2.74/1.00  --min_unsat_core                        false
% 2.74/1.00  --soft_assumptions                      false
% 2.74/1.00  --soft_lemma_size                       3
% 2.74/1.00  --prop_impl_unit_size                   0
% 2.74/1.00  --prop_impl_unit                        []
% 2.74/1.00  --share_sel_clauses                     true
% 2.74/1.00  --reset_solvers                         false
% 2.74/1.00  --bc_imp_inh                            [conj_cone]
% 2.74/1.00  --conj_cone_tolerance                   3.
% 2.74/1.00  --extra_neg_conj                        none
% 2.74/1.00  --large_theory_mode                     true
% 2.74/1.00  --prolific_symb_bound                   200
% 2.74/1.00  --lt_threshold                          2000
% 2.74/1.00  --clause_weak_htbl                      true
% 2.74/1.00  --gc_record_bc_elim                     false
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing Options
% 2.74/1.00  
% 2.74/1.00  --preprocessing_flag                    true
% 2.74/1.00  --time_out_prep_mult                    0.1
% 2.74/1.00  --splitting_mode                        input
% 2.74/1.00  --splitting_grd                         true
% 2.74/1.00  --splitting_cvd                         false
% 2.74/1.00  --splitting_cvd_svl                     false
% 2.74/1.00  --splitting_nvd                         32
% 2.74/1.00  --sub_typing                            true
% 2.74/1.00  --prep_gs_sim                           true
% 2.74/1.00  --prep_unflatten                        true
% 2.74/1.00  --prep_res_sim                          true
% 2.74/1.00  --prep_upred                            true
% 2.74/1.00  --prep_sem_filter                       exhaustive
% 2.74/1.00  --prep_sem_filter_out                   false
% 2.74/1.00  --pred_elim                             true
% 2.74/1.00  --res_sim_input                         true
% 2.74/1.00  --eq_ax_congr_red                       true
% 2.74/1.00  --pure_diseq_elim                       true
% 2.74/1.00  --brand_transform                       false
% 2.74/1.00  --non_eq_to_eq                          false
% 2.74/1.00  --prep_def_merge                        true
% 2.74/1.00  --prep_def_merge_prop_impl              false
% 2.74/1.00  --prep_def_merge_mbd                    true
% 2.74/1.00  --prep_def_merge_tr_red                 false
% 2.74/1.00  --prep_def_merge_tr_cl                  false
% 2.74/1.00  --smt_preprocessing                     true
% 2.74/1.00  --smt_ac_axioms                         fast
% 2.74/1.00  --preprocessed_out                      false
% 2.74/1.00  --preprocessed_stats                    false
% 2.74/1.00  
% 2.74/1.00  ------ Abstraction refinement Options
% 2.74/1.00  
% 2.74/1.00  --abstr_ref                             []
% 2.74/1.00  --abstr_ref_prep                        false
% 2.74/1.00  --abstr_ref_until_sat                   false
% 2.74/1.00  --abstr_ref_sig_restrict                funpre
% 2.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.00  --abstr_ref_under                       []
% 2.74/1.00  
% 2.74/1.00  ------ SAT Options
% 2.74/1.00  
% 2.74/1.00  --sat_mode                              false
% 2.74/1.00  --sat_fm_restart_options                ""
% 2.74/1.00  --sat_gr_def                            false
% 2.74/1.00  --sat_epr_types                         true
% 2.74/1.00  --sat_non_cyclic_types                  false
% 2.74/1.00  --sat_finite_models                     false
% 2.74/1.00  --sat_fm_lemmas                         false
% 2.74/1.00  --sat_fm_prep                           false
% 2.74/1.00  --sat_fm_uc_incr                        true
% 2.74/1.00  --sat_out_model                         small
% 2.74/1.00  --sat_out_clauses                       false
% 2.74/1.00  
% 2.74/1.00  ------ QBF Options
% 2.74/1.00  
% 2.74/1.00  --qbf_mode                              false
% 2.74/1.00  --qbf_elim_univ                         false
% 2.74/1.00  --qbf_dom_inst                          none
% 2.74/1.00  --qbf_dom_pre_inst                      false
% 2.74/1.00  --qbf_sk_in                             false
% 2.74/1.00  --qbf_pred_elim                         true
% 2.74/1.00  --qbf_split                             512
% 2.74/1.00  
% 2.74/1.00  ------ BMC1 Options
% 2.74/1.00  
% 2.74/1.00  --bmc1_incremental                      false
% 2.74/1.00  --bmc1_axioms                           reachable_all
% 2.74/1.00  --bmc1_min_bound                        0
% 2.74/1.00  --bmc1_max_bound                        -1
% 2.74/1.00  --bmc1_max_bound_default                -1
% 2.74/1.00  --bmc1_symbol_reachability              true
% 2.74/1.00  --bmc1_property_lemmas                  false
% 2.74/1.00  --bmc1_k_induction                      false
% 2.74/1.00  --bmc1_non_equiv_states                 false
% 2.74/1.00  --bmc1_deadlock                         false
% 2.74/1.00  --bmc1_ucm                              false
% 2.74/1.00  --bmc1_add_unsat_core                   none
% 2.74/1.00  --bmc1_unsat_core_children              false
% 2.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.00  --bmc1_out_stat                         full
% 2.74/1.00  --bmc1_ground_init                      false
% 2.74/1.00  --bmc1_pre_inst_next_state              false
% 2.74/1.00  --bmc1_pre_inst_state                   false
% 2.74/1.00  --bmc1_pre_inst_reach_state             false
% 2.74/1.00  --bmc1_out_unsat_core                   false
% 2.74/1.00  --bmc1_aig_witness_out                  false
% 2.74/1.00  --bmc1_verbose                          false
% 2.74/1.00  --bmc1_dump_clauses_tptp                false
% 2.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.00  --bmc1_dump_file                        -
% 2.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.00  --bmc1_ucm_extend_mode                  1
% 2.74/1.00  --bmc1_ucm_init_mode                    2
% 2.74/1.00  --bmc1_ucm_cone_mode                    none
% 2.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.00  --bmc1_ucm_relax_model                  4
% 2.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.00  --bmc1_ucm_layered_model                none
% 2.74/1.00  --bmc1_ucm_max_lemma_size               10
% 2.74/1.00  
% 2.74/1.00  ------ AIG Options
% 2.74/1.00  
% 2.74/1.00  --aig_mode                              false
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation Options
% 2.74/1.00  
% 2.74/1.00  --instantiation_flag                    true
% 2.74/1.00  --inst_sos_flag                         false
% 2.74/1.00  --inst_sos_phase                        true
% 2.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel_side                     none
% 2.74/1.00  --inst_solver_per_active                1400
% 2.74/1.00  --inst_solver_calls_frac                1.
% 2.74/1.00  --inst_passive_queue_type               priority_queues
% 2.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.00  --inst_passive_queues_freq              [25;2]
% 2.74/1.00  --inst_dismatching                      true
% 2.74/1.00  --inst_eager_unprocessed_to_passive     true
% 2.74/1.00  --inst_prop_sim_given                   true
% 2.74/1.00  --inst_prop_sim_new                     false
% 2.74/1.00  --inst_subs_new                         false
% 2.74/1.00  --inst_eq_res_simp                      false
% 2.74/1.00  --inst_subs_given                       false
% 2.74/1.00  --inst_orphan_elimination               true
% 2.74/1.00  --inst_learning_loop_flag               true
% 2.74/1.00  --inst_learning_start                   3000
% 2.74/1.00  --inst_learning_factor                  2
% 2.74/1.00  --inst_start_prop_sim_after_learn       3
% 2.74/1.00  --inst_sel_renew                        solver
% 2.74/1.00  --inst_lit_activity_flag                true
% 2.74/1.00  --inst_restr_to_given                   false
% 2.74/1.00  --inst_activity_threshold               500
% 2.74/1.00  --inst_out_proof                        true
% 2.74/1.00  
% 2.74/1.00  ------ Resolution Options
% 2.74/1.00  
% 2.74/1.00  --resolution_flag                       false
% 2.74/1.00  --res_lit_sel                           adaptive
% 2.74/1.00  --res_lit_sel_side                      none
% 2.74/1.00  --res_ordering                          kbo
% 2.74/1.00  --res_to_prop_solver                    active
% 2.74/1.00  --res_prop_simpl_new                    false
% 2.74/1.00  --res_prop_simpl_given                  true
% 2.74/1.00  --res_passive_queue_type                priority_queues
% 2.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.00  --res_passive_queues_freq               [15;5]
% 2.74/1.00  --res_forward_subs                      full
% 2.74/1.00  --res_backward_subs                     full
% 2.74/1.00  --res_forward_subs_resolution           true
% 2.74/1.00  --res_backward_subs_resolution          true
% 2.74/1.00  --res_orphan_elimination                true
% 2.74/1.00  --res_time_limit                        2.
% 2.74/1.00  --res_out_proof                         true
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Options
% 2.74/1.00  
% 2.74/1.00  --superposition_flag                    true
% 2.74/1.00  --sup_passive_queue_type                priority_queues
% 2.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.00  --demod_completeness_check              fast
% 2.74/1.00  --demod_use_ground                      true
% 2.74/1.00  --sup_to_prop_solver                    passive
% 2.74/1.00  --sup_prop_simpl_new                    true
% 2.74/1.00  --sup_prop_simpl_given                  true
% 2.74/1.00  --sup_fun_splitting                     false
% 2.74/1.00  --sup_smt_interval                      50000
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Simplification Setup
% 2.74/1.00  
% 2.74/1.00  --sup_indices_passive                   []
% 2.74/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_full_bw                           [BwDemod]
% 2.74/1.00  --sup_immed_triv                        [TrivRules]
% 2.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_immed_bw_main                     []
% 2.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  
% 2.74/1.00  ------ Combination Options
% 2.74/1.00  
% 2.74/1.00  --comb_res_mult                         3
% 2.74/1.00  --comb_sup_mult                         2
% 2.74/1.00  --comb_inst_mult                        10
% 2.74/1.00  
% 2.74/1.00  ------ Debug Options
% 2.74/1.00  
% 2.74/1.00  --dbg_backtrace                         false
% 2.74/1.00  --dbg_dump_prop_clauses                 false
% 2.74/1.00  --dbg_dump_prop_clauses_file            -
% 2.74/1.00  --dbg_out_stat                          false
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  ------ Proving...
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  % SZS status Theorem for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00   Resolution empty clause
% 2.74/1.00  
% 2.74/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  fof(f17,conjecture,(
% 2.74/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f18,negated_conjecture,(
% 2.74/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.74/1.00    inference(negated_conjecture,[],[f17])).
% 2.74/1.00  
% 2.74/1.00  fof(f37,plain,(
% 2.74/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.74/1.00    inference(ennf_transformation,[],[f18])).
% 2.74/1.00  
% 2.74/1.00  fof(f38,plain,(
% 2.74/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.74/1.00    inference(flattening,[],[f37])).
% 2.74/1.00  
% 2.74/1.00  fof(f42,plain,(
% 2.74/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.74/1.00    introduced(choice_axiom,[])).
% 2.74/1.00  
% 2.74/1.00  fof(f43,plain,(
% 2.74/1.00    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42])).
% 2.74/1.00  
% 2.74/1.00  fof(f70,plain,(
% 2.74/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f9,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f19,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.74/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.74/1.00  
% 2.74/1.00  fof(f26,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f19])).
% 2.74/1.00  
% 2.74/1.00  fof(f54,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f26])).
% 2.74/1.00  
% 2.74/1.00  fof(f6,axiom,(
% 2.74/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f23,plain,(
% 2.74/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.74/1.00    inference(ennf_transformation,[],[f6])).
% 2.74/1.00  
% 2.74/1.00  fof(f40,plain,(
% 2.74/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.74/1.00    inference(nnf_transformation,[],[f23])).
% 2.74/1.00  
% 2.74/1.00  fof(f50,plain,(
% 2.74/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f40])).
% 2.74/1.00  
% 2.74/1.00  fof(f8,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f25,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f8])).
% 2.74/1.00  
% 2.74/1.00  fof(f53,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f25])).
% 2.74/1.00  
% 2.74/1.00  fof(f12,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f29,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f12])).
% 2.74/1.00  
% 2.74/1.00  fof(f57,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f29])).
% 2.74/1.00  
% 2.74/1.00  fof(f71,plain,(
% 2.74/1.00    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f13,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f30,plain,(
% 2.74/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.74/1.00    inference(ennf_transformation,[],[f13])).
% 2.74/1.00  
% 2.74/1.00  fof(f31,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.74/1.00    inference(flattening,[],[f30])).
% 2.74/1.00  
% 2.74/1.00  fof(f58,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f31])).
% 2.74/1.00  
% 2.74/1.00  fof(f4,axiom,(
% 2.74/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f21,plain,(
% 2.74/1.00    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.74/1.00    inference(ennf_transformation,[],[f4])).
% 2.74/1.00  
% 2.74/1.00  fof(f22,plain,(
% 2.74/1.00    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.74/1.00    inference(flattening,[],[f21])).
% 2.74/1.00  
% 2.74/1.00  fof(f47,plain,(
% 2.74/1.00    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f22])).
% 2.74/1.00  
% 2.74/1.00  fof(f3,axiom,(
% 2.74/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f46,plain,(
% 2.74/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f3])).
% 2.74/1.00  
% 2.74/1.00  fof(f2,axiom,(
% 2.74/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f45,plain,(
% 2.74/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f2])).
% 2.74/1.00  
% 2.74/1.00  fof(f16,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f35,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f16])).
% 2.74/1.00  
% 2.74/1.00  fof(f36,plain,(
% 2.74/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(flattening,[],[f35])).
% 2.74/1.00  
% 2.74/1.00  fof(f41,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(nnf_transformation,[],[f36])).
% 2.74/1.00  
% 2.74/1.00  fof(f62,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f41])).
% 2.74/1.00  
% 2.74/1.00  fof(f69,plain,(
% 2.74/1.00    v1_funct_2(sK3,sK0,sK1)),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f11,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f28,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f11])).
% 2.74/1.00  
% 2.74/1.00  fof(f56,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f28])).
% 2.74/1.00  
% 2.74/1.00  fof(f7,axiom,(
% 2.74/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f24,plain,(
% 2.74/1.00    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f7])).
% 2.74/1.00  
% 2.74/1.00  fof(f52,plain,(
% 2.74/1.00    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f24])).
% 2.74/1.00  
% 2.74/1.00  fof(f66,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f41])).
% 2.74/1.00  
% 2.74/1.00  fof(f76,plain,(
% 2.74/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.74/1.00    inference(equality_resolution,[],[f66])).
% 2.74/1.00  
% 2.74/1.00  fof(f72,plain,(
% 2.74/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f1,axiom,(
% 2.74/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f20,plain,(
% 2.74/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f1])).
% 2.74/1.00  
% 2.74/1.00  fof(f44,plain,(
% 2.74/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f20])).
% 2.74/1.00  
% 2.74/1.00  fof(f73,plain,(
% 2.74/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f68,plain,(
% 2.74/1.00    v1_funct_1(sK3)),
% 2.74/1.00    inference(cnf_transformation,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f15,axiom,(
% 2.74/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f34,plain,(
% 2.74/1.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f15])).
% 2.74/1.00  
% 2.74/1.00  fof(f61,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f34])).
% 2.74/1.00  
% 2.74/1.00  fof(f14,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f32,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f14])).
% 2.74/1.00  
% 2.74/1.00  fof(f33,plain,(
% 2.74/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(flattening,[],[f32])).
% 2.74/1.00  
% 2.74/1.00  fof(f60,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f33])).
% 2.74/1.00  
% 2.74/1.00  fof(f10,axiom,(
% 2.74/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f27,plain,(
% 2.74/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f10])).
% 2.74/1.00  
% 2.74/1.00  fof(f55,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f27])).
% 2.74/1.00  
% 2.74/1.00  fof(f64,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f41])).
% 2.74/1.00  
% 2.74/1.00  cnf(c_27,negated_conjecture,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.74/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1546,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_10,plain,
% 2.74/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.74/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_7,plain,
% 2.74/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_440,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.74/1.00      | ~ v1_relat_1(X0) ),
% 2.74/1.00      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_9,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_444,plain,
% 2.74/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.74/1.00      inference(global_propositional_subsumption,[status(thm)],[c_440,c_9]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_445,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.74/1.00      inference(renaming,[status(thm)],[c_444]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1544,plain,
% 2.74/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2772,plain,
% 2.74/1.00      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1546,c_1544]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_13,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1549,plain,
% 2.74/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.74/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2489,plain,
% 2.74/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1546,c_1549]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_26,negated_conjecture,
% 2.74/1.00      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 2.74/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1547,plain,
% 2.74/1.00      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2589,plain,
% 2.74/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_2489,c_1547]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_14,plain,
% 2.74/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.74/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.74/1.00      | ~ v1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1548,plain,
% 2.74/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.74/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.74/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2863,plain,
% 2.74/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.74/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.74/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1548,c_1549]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6261,plain,
% 2.74/1.00      ( k2_relset_1(X0,sK2,sK3) = k2_relat_1(sK3)
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2589,c_2863]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_32,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3,plain,
% 2.74/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_91,plain,
% 2.74/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.74/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.74/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_93,plain,
% 2.74/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.74/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.74/1.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_91]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2,plain,
% 2.74/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_94,plain,
% 2.74/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_96,plain,
% 2.74/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_94]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1,plain,
% 2.74/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_97,plain,
% 2.74/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_99,plain,
% 2.74/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_97]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1775,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.74/1.00      | v1_relat_1(sK3) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1776,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1789,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_445]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1790,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_23,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.74/1.00      | k1_xboole_0 = X2 ),
% 2.74/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_28,negated_conjecture,
% 2.74/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_503,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.74/1.00      | sK1 != X2
% 2.74/1.00      | sK0 != X1
% 2.74/1.00      | sK3 != X0
% 2.74/1.00      | k1_xboole_0 = X2 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_504,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.74/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.74/1.00      | k1_xboole_0 = sK1 ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_503]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_506,plain,
% 2.74/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.74/1.00      inference(global_propositional_subsumption,[status(thm)],[c_504,c_27]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_12,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1550,plain,
% 2.74/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.74/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2503,plain,
% 2.74/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1546,c_1550]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2627,plain,
% 2.74/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_506,c_2503]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_8,plain,
% 2.74/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1553,plain,
% 2.74/1.00      ( v1_xboole_0(X0) != iProver_top
% 2.74/1.00      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2683,plain,
% 2.74/1.00      ( sK1 = k1_xboole_0
% 2.74/1.00      | v1_xboole_0(sK0) = iProver_top
% 2.74/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2627,c_1553]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_943,plain,
% 2.74/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.74/1.00      theory(equality) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1778,plain,
% 2.74/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_943]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1779,plain,
% 2.74/1.00      ( sK0 != X0
% 2.74/1.00      | v1_xboole_0(X0) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1781,plain,
% 2.74/1.00      ( sK0 != k1_xboole_0
% 2.74/1.00      | v1_xboole_0(sK0) = iProver_top
% 2.74/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_1779]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_942,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1792,plain,
% 2.74/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_942]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1847,plain,
% 2.74/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_1792]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_941,plain,( X0 = X0 ),theory(equality) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1848,plain,
% 2.74/1.00      ( sK0 = sK0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_941]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_19,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.74/1.00      | k1_xboole_0 = X1
% 2.74/1.00      | k1_xboole_0 = X0 ),
% 2.74/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_558,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.74/1.00      | sK1 != k1_xboole_0
% 2.74/1.00      | sK0 != X1
% 2.74/1.00      | sK3 != X0
% 2.74/1.00      | k1_xboole_0 = X0
% 2.74/1.00      | k1_xboole_0 = X1 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_559,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.74/1.00      | sK1 != k1_xboole_0
% 2.74/1.00      | k1_xboole_0 = sK0
% 2.74/1.00      | k1_xboole_0 = sK3 ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1540,plain,
% 2.74/1.00      ( sK1 != k1_xboole_0
% 2.74/1.00      | k1_xboole_0 = sK0
% 2.74/1.00      | k1_xboole_0 = sK3
% 2.74/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_25,negated_conjecture,
% 2.74/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.74/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_92,plain,
% 2.74/1.00      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.74/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.74/1.00      | v1_xboole_0(k1_xboole_0) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_95,plain,
% 2.74/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_98,plain,
% 2.74/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_0,plain,
% 2.74/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.74/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_101,plain,
% 2.74/1.00      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1936,plain,
% 2.74/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_942]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1937,plain,
% 2.74/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_1936]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2171,plain,
% 2.74/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_1540,c_25,c_92,c_95,c_98,c_101,c_1937]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2690,plain,
% 2.74/1.00      ( v1_xboole_0(sK0) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2683,c_93,c_96,c_99,c_1781,c_1847,c_1848,c_2171]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_24,negated_conjecture,
% 2.74/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | ~ v1_funct_1(sK3) ),
% 2.74/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_29,negated_conjecture,
% 2.74/1.00      ( v1_funct_1(sK3) ),
% 2.74/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_166,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.74/1.00      inference(global_propositional_subsumption,[status(thm)],[c_24,c_29]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_167,negated_conjecture,
% 2.74/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.74/1.00      inference(renaming,[status(thm)],[c_166]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_17,plain,
% 2.74/1.00      ( v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v1_xboole_0(X1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_15,plain,
% 2.74/1.00      ( v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v1_funct_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_398,plain,
% 2.74/1.00      ( v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | sK3 != X0 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_399,plain,
% 2.74/1.00      ( v1_funct_2(sK3,X0,X1)
% 2.74/1.00      | ~ v1_partfun1(sK3,X0)
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_417,plain,
% 2.74/1.00      ( v1_funct_2(sK3,X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.00      | ~ v1_xboole_0(X3)
% 2.74/1.00      | X0 != X3
% 2.74/1.00      | sK3 != X2 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_399]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_418,plain,
% 2.74/1.00      ( v1_funct_2(sK3,X0,X1)
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.00      | ~ v1_xboole_0(X0) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_641,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | ~ v1_xboole_0(X0)
% 2.74/1.00      | sK2 != X1
% 2.74/1.00      | sK0 != X0
% 2.74/1.00      | sK3 != sK3 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_167,c_418]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_642,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | ~ v1_xboole_0(sK0) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_641]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_936,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | ~ v1_xboole_0(sK0)
% 2.74/1.00      | sP0_iProver_split ),
% 2.74/1.00      inference(splitting,
% 2.74/1.00                [splitting(split),new_symbols(definition,[])],
% 2.74/1.00                [c_642]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1533,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK0) != iProver_top
% 2.74/1.00      | sP0_iProver_split = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_935,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.74/1.00      | ~ sP0_iProver_split ),
% 2.74/1.00      inference(splitting,
% 2.74/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.74/1.00                [c_642]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1534,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.74/1.00      | sP0_iProver_split != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1627,plain,
% 2.74/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.74/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1533,c_1534]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2867,plain,
% 2.74/1.00      ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1548,c_1627]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3298,plain,
% 2.74/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_943]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3299,plain,
% 2.74/1.00      ( sK2 != X0
% 2.74/1.00      | v1_xboole_0(X0) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_3298]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3301,plain,
% 2.74/1.00      ( sK2 != k1_xboole_0
% 2.74/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.74/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_3299]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_11,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v1_xboole_0(X2)
% 2.74/1.00      | v1_xboole_0(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1551,plain,
% 2.74/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.74/1.00      | v1_xboole_0(X2) != iProver_top
% 2.74/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2864,plain,
% 2.74/1.00      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 2.74/1.00      | v1_relat_1(X0) != iProver_top
% 2.74/1.00      | v1_xboole_0(X1) != iProver_top
% 2.74/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1548,c_1551]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6050,plain,
% 2.74/1.00      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK2) != iProver_top
% 2.74/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2589,c_2864]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2862,plain,
% 2.74/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.74/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.74/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1548,c_1550]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6083,plain,
% 2.74/1.00      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2589,c_2862]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6362,plain,
% 2.74/1.00      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.74/1.00      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_6083,c_32,c_1776]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6363,plain,
% 2.74/1.00      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.74/1.00      inference(renaming,[status(thm)],[c_6362]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6371,plain,
% 2.74/1.00      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2772,c_6363]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_21,plain,
% 2.74/1.00      ( v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.74/1.00      | k1_xboole_0 = X2 ),
% 2.74/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_490,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.74/1.00      | sK2 != X2
% 2.74/1.00      | sK0 != X1
% 2.74/1.00      | sK3 != X0
% 2.74/1.00      | k1_xboole_0 = X2 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_167]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_491,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.74/1.00      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.74/1.00      | k1_xboole_0 = sK2 ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1543,plain,
% 2.74/1.00      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 2.74/1.00      | k1_xboole_0 = sK2
% 2.74/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6579,plain,
% 2.74/1.00      ( k1_relat_1(sK3) != sK0
% 2.74/1.00      | sK2 = k1_xboole_0
% 2.74/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_6371,c_1543]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6582,plain,
% 2.74/1.00      ( sK2 = k1_xboole_0
% 2.74/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_6579,c_32,c_93,c_96,c_99,c_1776,c_1781,c_1790,c_1847,
% 2.74/1.00                 c_1848,c_2171,c_2589,c_2627,c_2867]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6589,plain,
% 2.74/1.00      ( sK2 = k1_xboole_0
% 2.74/1.00      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 2.74/1.00      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 2.74/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1548,c_6582]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6698,plain,
% 2.74/1.00      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_6261,c_32,c_93,c_96,c_99,c_1776,c_1790,c_2589,c_2690,
% 2.74/1.00                 c_2867,c_3301,c_6050,c_6589]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6706,plain,
% 2.74/1.00      ( $false ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2772,c_6698]) ).
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  ------                               Statistics
% 2.74/1.00  
% 2.74/1.00  ------ General
% 2.74/1.00  
% 2.74/1.00  abstr_ref_over_cycles:                  0
% 2.74/1.00  abstr_ref_under_cycles:                 0
% 2.74/1.00  gc_basic_clause_elim:                   0
% 2.74/1.00  forced_gc_time:                         0
% 2.74/1.00  parsing_time:                           0.01
% 2.74/1.00  unif_index_cands_time:                  0.
% 2.74/1.00  unif_index_add_time:                    0.
% 2.74/1.00  orderings_time:                         0.
% 2.74/1.00  out_proof_time:                         0.009
% 2.74/1.00  total_time:                             0.197
% 2.74/1.00  num_of_symbols:                         54
% 2.74/1.00  num_of_terms:                           3629
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing
% 2.74/1.00  
% 2.74/1.00  num_of_splits:                          3
% 2.74/1.00  num_of_split_atoms:                     3
% 2.74/1.00  num_of_reused_defs:                     0
% 2.74/1.00  num_eq_ax_congr_red:                    16
% 2.74/1.00  num_of_sem_filtered_clauses:            3
% 2.74/1.00  num_of_subtypes:                        0
% 2.74/1.00  monotx_restored_types:                  0
% 2.74/1.00  sat_num_of_epr_types:                   0
% 2.74/1.00  sat_num_of_non_cyclic_types:            0
% 2.74/1.00  sat_guarded_non_collapsed_types:        0
% 2.74/1.00  num_pure_diseq_elim:                    0
% 2.74/1.00  simp_replaced_by:                       0
% 2.74/1.00  res_preprocessed:                       127
% 2.74/1.00  prep_upred:                             0
% 2.74/1.00  prep_unflattend:                        49
% 2.74/1.00  smt_new_axioms:                         0
% 2.74/1.00  pred_elim_cands:                        4
% 2.74/1.00  pred_elim:                              5
% 2.74/1.00  pred_elim_cl:                           4
% 2.74/1.00  pred_elim_cycles:                       8
% 2.74/1.00  merged_defs:                            8
% 2.74/1.00  merged_defs_ncl:                        0
% 2.74/1.00  bin_hyper_res:                          8
% 2.74/1.00  prep_cycles:                            4
% 2.74/1.00  pred_elim_time:                         0.008
% 2.74/1.00  splitting_time:                         0.
% 2.74/1.00  sem_filter_time:                        0.
% 2.74/1.00  monotx_time:                            0.
% 2.74/1.00  subtype_inf_time:                       0.
% 2.74/1.00  
% 2.74/1.00  ------ Problem properties
% 2.74/1.00  
% 2.74/1.00  clauses:                                28
% 2.74/1.00  conjectures:                            3
% 2.74/1.00  epr:                                    5
% 2.74/1.00  horn:                                   24
% 2.74/1.00  ground:                                 12
% 2.74/1.00  unary:                                  3
% 2.74/1.00  binary:                                 15
% 2.74/1.00  lits:                                   70
% 2.74/1.00  lits_eq:                                23
% 2.74/1.00  fd_pure:                                0
% 2.74/1.00  fd_pseudo:                              0
% 2.74/1.00  fd_cond:                                1
% 2.74/1.00  fd_pseudo_cond:                         0
% 2.74/1.00  ac_symbols:                             0
% 2.74/1.00  
% 2.74/1.00  ------ Propositional Solver
% 2.74/1.00  
% 2.74/1.00  prop_solver_calls:                      30
% 2.74/1.00  prop_fast_solver_calls:                 1092
% 2.74/1.00  smt_solver_calls:                       0
% 2.74/1.00  smt_fast_solver_calls:                  0
% 2.74/1.00  prop_num_of_clauses:                    2007
% 2.74/1.00  prop_preprocess_simplified:             6474
% 2.74/1.00  prop_fo_subsumed:                       39
% 2.74/1.00  prop_solver_time:                       0.
% 2.74/1.00  smt_solver_time:                        0.
% 2.74/1.00  smt_fast_solver_time:                   0.
% 2.74/1.00  prop_fast_solver_time:                  0.
% 2.74/1.00  prop_unsat_core_time:                   0.
% 2.74/1.00  
% 2.74/1.00  ------ QBF
% 2.74/1.00  
% 2.74/1.00  qbf_q_res:                              0
% 2.74/1.00  qbf_num_tautologies:                    0
% 2.74/1.00  qbf_prep_cycles:                        0
% 2.74/1.00  
% 2.74/1.00  ------ BMC1
% 2.74/1.00  
% 2.74/1.00  bmc1_current_bound:                     -1
% 2.74/1.00  bmc1_last_solved_bound:                 -1
% 2.74/1.00  bmc1_unsat_core_size:                   -1
% 2.74/1.00  bmc1_unsat_core_parents_size:           -1
% 2.74/1.00  bmc1_merge_next_fun:                    0
% 2.74/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation
% 2.74/1.00  
% 2.74/1.00  inst_num_of_clauses:                    604
% 2.74/1.00  inst_num_in_passive:                    155
% 2.74/1.00  inst_num_in_active:                     447
% 2.74/1.00  inst_num_in_unprocessed:                2
% 2.74/1.00  inst_num_of_loops:                      520
% 2.74/1.00  inst_num_of_learning_restarts:          0
% 2.74/1.00  inst_num_moves_active_passive:          68
% 2.74/1.00  inst_lit_activity:                      0
% 2.74/1.00  inst_lit_activity_moves:                0
% 2.74/1.00  inst_num_tautologies:                   0
% 2.74/1.00  inst_num_prop_implied:                  0
% 2.74/1.00  inst_num_existing_simplified:           0
% 2.74/1.00  inst_num_eq_res_simplified:             0
% 2.74/1.00  inst_num_child_elim:                    0
% 2.74/1.00  inst_num_of_dismatching_blockings:      243
% 2.74/1.00  inst_num_of_non_proper_insts:           1080
% 2.74/1.00  inst_num_of_duplicates:                 0
% 2.74/1.00  inst_inst_num_from_inst_to_res:         0
% 2.74/1.00  inst_dismatching_checking_time:         0.
% 2.74/1.00  
% 2.74/1.00  ------ Resolution
% 2.74/1.00  
% 2.74/1.00  res_num_of_clauses:                     0
% 2.74/1.00  res_num_in_passive:                     0
% 2.74/1.00  res_num_in_active:                      0
% 2.74/1.00  res_num_of_loops:                       131
% 2.74/1.00  res_forward_subset_subsumed:            43
% 2.74/1.00  res_backward_subset_subsumed:           0
% 2.74/1.00  res_forward_subsumed:                   0
% 2.74/1.00  res_backward_subsumed:                  0
% 2.74/1.00  res_forward_subsumption_resolution:     0
% 2.74/1.00  res_backward_subsumption_resolution:    0
% 2.74/1.00  res_clause_to_clause_subsumption:       917
% 2.74/1.00  res_orphan_elimination:                 0
% 2.74/1.00  res_tautology_del:                      170
% 2.74/1.00  res_num_eq_res_simplified:              1
% 2.74/1.00  res_num_sel_changes:                    0
% 2.74/1.00  res_moves_from_active_to_pass:          0
% 2.74/1.00  
% 2.74/1.00  ------ Superposition
% 2.74/1.00  
% 2.74/1.00  sup_time_total:                         0.
% 2.74/1.00  sup_time_generating:                    0.
% 2.74/1.00  sup_time_sim_full:                      0.
% 2.74/1.00  sup_time_sim_immed:                     0.
% 2.74/1.00  
% 2.74/1.00  sup_num_of_clauses:                     115
% 2.74/1.00  sup_num_in_active:                      100
% 2.74/1.00  sup_num_in_passive:                     15
% 2.74/1.00  sup_num_of_loops:                       102
% 2.74/1.00  sup_fw_superposition:                   104
% 2.74/1.00  sup_bw_superposition:                   39
% 2.74/1.00  sup_immediate_simplified:               31
% 2.74/1.00  sup_given_eliminated:                   0
% 2.74/1.00  comparisons_done:                       0
% 2.74/1.00  comparisons_avoided:                    10
% 2.74/1.00  
% 2.74/1.00  ------ Simplifications
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  sim_fw_subset_subsumed:                 9
% 2.74/1.00  sim_bw_subset_subsumed:                 2
% 2.74/1.00  sim_fw_subsumed:                        4
% 2.74/1.00  sim_bw_subsumed:                        0
% 2.74/1.00  sim_fw_subsumption_res:                 2
% 2.74/1.00  sim_bw_subsumption_res:                 0
% 2.74/1.00  sim_tautology_del:                      5
% 2.74/1.00  sim_eq_tautology_del:                   21
% 2.74/1.00  sim_eq_res_simp:                        0
% 2.74/1.00  sim_fw_demodulated:                     1
% 2.74/1.00  sim_bw_demodulated:                     2
% 2.74/1.00  sim_light_normalised:                   22
% 2.74/1.00  sim_joinable_taut:                      0
% 2.74/1.00  sim_joinable_simp:                      0
% 2.74/1.00  sim_ac_normalised:                      0
% 2.74/1.00  sim_smt_subsumption:                    0
% 2.74/1.00  
%------------------------------------------------------------------------------
