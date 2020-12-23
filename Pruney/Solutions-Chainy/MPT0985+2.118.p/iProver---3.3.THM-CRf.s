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
% DateTime   : Thu Dec  3 12:02:44 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  244 (56760 expanded)
%              Number of clauses        :  179 (18764 expanded)
%              Number of leaves         :   18 (10887 expanded)
%              Depth                    :   32
%              Number of atoms          :  813 (302395 expanded)
%              Number of equality atoms :  439 (64590 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f33,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,
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

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1549,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_644,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_646,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_29])).

cnf(c_1535,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1540,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2570,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1535,c_1540])).

cnf(c_2703,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_646,c_2570])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1542,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2173,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1542])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1544,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4132,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_1544])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1851,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1922,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4466,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4132,c_31,c_29,c_28,c_1851,c_1922])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_466,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_450,c_23])).

cnf(c_1531,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_5379,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k2_funct_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4466,c_1531])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1543,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4092,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_1543])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1539,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2524,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1535,c_1539])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2526,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2524,c_27])).

cnf(c_4103,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4092,c_2526])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4301,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_32,c_35])).

cnf(c_5407,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5379,c_4301])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1852,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1851])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1925,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1929,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1924,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1931,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_6194,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5407,c_32,c_34,c_35,c_1852,c_1929,c_1931])).

cnf(c_6201,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_6194])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_628,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_629,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_786,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2012,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_788,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1995,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2374,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_3170,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3171,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4469,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4466,c_1538])).

cnf(c_4485,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4469,c_4301])).

cnf(c_4557,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4485,c_32,c_34,c_35,c_1852,c_1929,c_1931])).

cnf(c_4562,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_4557])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1541,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3064,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_1541])).

cnf(c_3765,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_34])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3771,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_1548])).

cnf(c_1537,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4318,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4301,c_1537])).

cnf(c_4954,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4318,c_32,c_34,c_35,c_1852,c_1929,c_1931])).

cnf(c_4960,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4954,c_4466])).

cnf(c_4967,plain,
    ( k1_relset_1(sK1,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_1540])).

cnf(c_4977,plain,
    ( k1_relset_1(sK1,X0,k2_funct_1(sK2)) = sK1
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4967,c_4301])).

cnf(c_4997,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_3771,c_4977])).

cnf(c_6202,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6201])).

cnf(c_6204,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6201,c_32,c_34,c_35,c_629,c_1852,c_1929,c_2012,c_3170,c_3171,c_4562,c_4997,c_6202])).

cnf(c_6205,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6204])).

cnf(c_1523,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_6224,plain,
    ( k1_relset_1(sK1,sK0,k1_xboole_0) != sK1
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6205,c_1523])).

cnf(c_787,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1883,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_2011,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_7072,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6224,c_32,c_34,c_35,c_629,c_1852,c_1929,c_2011,c_2012,c_4997])).

cnf(c_7073,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7072])).

cnf(c_7078,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_7073])).

cnf(c_7080,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_7073])).

cnf(c_7176,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7078,c_3771,c_7080])).

cnf(c_7198,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7176,c_2570])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_564,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_1526,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_7204,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7176,c_1526])).

cnf(c_7216,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7204])).

cnf(c_7206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7176,c_1535])).

cnf(c_7219,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7216,c_7206])).

cnf(c_7244,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7198,c_7219])).

cnf(c_8819,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7244,c_4466])).

cnf(c_9349,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8819,c_1538])).

cnf(c_4563,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_1548])).

cnf(c_4761,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_4563])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1551,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5101,plain,
    ( k2_zfmisc_1(sK1,sK0) = k2_funct_1(sK2)
    | sK1 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_1551])).

cnf(c_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_107,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_789,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_801,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1912,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_2076,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_3396,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_3398,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3396])).

cnf(c_673,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_674,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_686,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_674,c_10])).

cnf(c_1521,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_675,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1950,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_32,c_34,c_35,c_675,c_1852,c_1929,c_1931])).

cnf(c_1951,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1950])).

cnf(c_4305,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4301,c_1951])).

cnf(c_4306,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4305])).

cnf(c_4316,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4306])).

cnf(c_4496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X2))
    | k1_relat_1(sK2) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_4498,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4496])).

cnf(c_4581,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4562])).

cnf(c_6484,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(X0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_6485,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6484])).

cnf(c_7632,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5101,c_31,c_29,c_28,c_100,c_103,c_107,c_801,c_1851,c_1922,c_2194,c_3398,c_3771,c_4316,c_4498,c_4581,c_6485,c_7080,c_7244])).

cnf(c_7649,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7632,c_4301])).

cnf(c_9365,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9349,c_7649])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_545,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_1527,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_546,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2244,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1527,c_32,c_34,c_35,c_546,c_1852,c_1929])).

cnf(c_2245,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2244])).

cnf(c_7201,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7176,c_2245])).

cnf(c_8743,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7201,c_31,c_29,c_28,c_100,c_103,c_107,c_801,c_1851,c_1922,c_2194,c_3398,c_3771,c_4316,c_4498,c_4581,c_6485,c_7080,c_7244])).

cnf(c_2215,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_6436,plain,
    ( k2_relat_1(sK2) != sK1
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_4957,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4954])).

cnf(c_2844,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != X0
    | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_4928,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_4749,plain,
    ( k2_relat_1(sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_4750,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4749])).

cnf(c_2742,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X2)
    | X2 != X1
    | k2_relat_1(k2_funct_1(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2743,plain,
    ( X0 != X1
    | k2_relat_1(k2_funct_1(sK2)) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2742])).

cnf(c_2745,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_2343,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_2344,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | X3 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_519,c_10])).

cnf(c_2154,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_2163,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_2165,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_1921,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_102,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9365,c_8819,c_8743,c_7244,c_7080,c_6485,c_6436,c_4957,c_4928,c_4750,c_4581,c_4498,c_4316,c_3771,c_3398,c_2745,c_2526,c_2344,c_2194,c_2165,c_1921,c_1922,c_1931,c_1929,c_1852,c_1851,c_801,c_107,c_104,c_103,c_100,c_35,c_28,c_34,c_29,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.00/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.99  
% 3.00/0.99  ------  iProver source info
% 3.00/0.99  
% 3.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.99  git: non_committed_changes: false
% 3.00/0.99  git: last_make_outside_of_git: false
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     num_symb
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       true
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  ------ Parsing...
% 3.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.99  ------ Proving...
% 3.00/0.99  ------ Problem Properties 
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  clauses                                 34
% 3.00/0.99  conjectures                             4
% 3.00/0.99  EPR                                     4
% 3.00/0.99  Horn                                    28
% 3.00/0.99  unary                                   5
% 3.00/0.99  binary                                  7
% 3.00/0.99  lits                                    111
% 3.00/0.99  lits eq                                 38
% 3.00/0.99  fd_pure                                 0
% 3.00/0.99  fd_pseudo                               0
% 3.00/0.99  fd_cond                                 3
% 3.00/0.99  fd_pseudo_cond                          1
% 3.00/0.99  AC symbols                              0
% 3.00/0.99  
% 3.00/0.99  ------ Schedule dynamic 5 is on 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  Current options:
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     none
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       false
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ Proving...
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS status Theorem for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  fof(f2,axiom,(
% 3.00/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f32,plain,(
% 3.00/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.00/0.99    inference(nnf_transformation,[],[f2])).
% 3.00/0.99  
% 3.00/0.99  fof(f40,plain,(
% 3.00/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f32])).
% 3.00/0.99  
% 3.00/0.99  fof(f9,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f22,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(ennf_transformation,[],[f9])).
% 3.00/0.99  
% 3.00/0.99  fof(f23,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(flattening,[],[f22])).
% 3.00/0.99  
% 3.00/0.99  fof(f33,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(nnf_transformation,[],[f23])).
% 3.00/0.99  
% 3.00/0.99  fof(f50,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f12,conjecture,(
% 3.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f13,negated_conjecture,(
% 3.00/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.00/0.99    inference(negated_conjecture,[],[f12])).
% 3.00/0.99  
% 3.00/0.99  fof(f28,plain,(
% 3.00/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.00/0.99    inference(ennf_transformation,[],[f13])).
% 3.00/0.99  
% 3.00/0.99  fof(f29,plain,(
% 3.00/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.00/0.99    inference(flattening,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f34,plain,(
% 3.00/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f35,plain,(
% 3.00/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34])).
% 3.00/0.99  
% 3.00/0.99  fof(f63,plain,(
% 3.00/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f64,plain,(
% 3.00/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f7,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f20,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(ennf_transformation,[],[f7])).
% 3.00/0.99  
% 3.00/0.99  fof(f48,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f20])).
% 3.00/0.99  
% 3.00/0.99  fof(f5,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f18,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(ennf_transformation,[],[f5])).
% 3.00/0.99  
% 3.00/0.99  fof(f46,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f18])).
% 3.00/0.99  
% 3.00/0.99  fof(f4,axiom,(
% 3.00/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f16,plain,(
% 3.00/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f4])).
% 3.00/0.99  
% 3.00/0.99  fof(f17,plain,(
% 3.00/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.99    inference(flattening,[],[f16])).
% 3.00/0.99  
% 3.00/0.99  fof(f45,plain,(
% 3.00/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f17])).
% 3.00/0.99  
% 3.00/0.99  fof(f62,plain,(
% 3.00/0.99    v1_funct_1(sK2)),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f65,plain,(
% 3.00/0.99    v2_funct_1(sK2)),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f54,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f72,plain,(
% 3.00/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.00/0.99    inference(equality_resolution,[],[f54])).
% 3.00/0.99  
% 3.00/0.99  fof(f11,axiom,(
% 3.00/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f26,plain,(
% 3.00/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/0.99    inference(ennf_transformation,[],[f11])).
% 3.00/0.99  
% 3.00/0.99  fof(f27,plain,(
% 3.00/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.00/0.99    inference(flattening,[],[f26])).
% 3.00/0.99  
% 3.00/0.99  fof(f60,plain,(
% 3.00/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f27])).
% 3.00/0.99  
% 3.00/0.99  fof(f61,plain,(
% 3.00/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f27])).
% 3.00/0.99  
% 3.00/0.99  fof(f44,plain,(
% 3.00/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f17])).
% 3.00/0.99  
% 3.00/0.99  fof(f8,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f21,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(ennf_transformation,[],[f8])).
% 3.00/0.99  
% 3.00/0.99  fof(f49,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f21])).
% 3.00/0.99  
% 3.00/0.99  fof(f66,plain,(
% 3.00/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f3,axiom,(
% 3.00/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f14,plain,(
% 3.00/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f3])).
% 3.00/0.99  
% 3.00/0.99  fof(f15,plain,(
% 3.00/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.99    inference(flattening,[],[f14])).
% 3.00/0.99  
% 3.00/0.99  fof(f42,plain,(
% 3.00/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f41,plain,(
% 3.00/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f52,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f67,plain,(
% 3.00/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.00/0.99    inference(cnf_transformation,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f1,axiom,(
% 3.00/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f30,plain,(
% 3.00/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.99    inference(nnf_transformation,[],[f1])).
% 3.00/0.99  
% 3.00/0.99  fof(f31,plain,(
% 3.00/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.99    inference(flattening,[],[f30])).
% 3.00/0.99  
% 3.00/0.99  fof(f36,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.00/0.99    inference(cnf_transformation,[],[f31])).
% 3.00/0.99  
% 3.00/0.99  fof(f69,plain,(
% 3.00/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/0.99    inference(equality_resolution,[],[f36])).
% 3.00/0.99  
% 3.00/0.99  fof(f10,axiom,(
% 3.00/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f24,plain,(
% 3.00/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f10])).
% 3.00/0.99  
% 3.00/0.99  fof(f25,plain,(
% 3.00/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.99    inference(flattening,[],[f24])).
% 3.00/0.99  
% 3.00/0.99  fof(f58,plain,(
% 3.00/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f25])).
% 3.00/0.99  
% 3.00/0.99  fof(f6,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.00/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f19,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.99    inference(ennf_transformation,[],[f6])).
% 3.00/0.99  
% 3.00/0.99  fof(f47,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f19])).
% 3.00/0.99  
% 3.00/0.99  fof(f39,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f32])).
% 3.00/0.99  
% 3.00/0.99  fof(f51,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f74,plain,(
% 3.00/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.00/0.99    inference(equality_resolution,[],[f51])).
% 3.00/0.99  
% 3.00/0.99  fof(f38,plain,(
% 3.00/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f31])).
% 3.00/0.99  
% 3.00/0.99  fof(f53,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f73,plain,(
% 3.00/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_relset_1(k1_xboole_0,X1,X2) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.00/0.99    inference(equality_resolution,[],[f53])).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1549,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.00/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_19,plain,
% 3.00/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.00/0.99      | k1_xboole_0 = X2 ),
% 3.00/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_30,negated_conjecture,
% 3.00/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_643,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.00/0.99      | sK0 != X1
% 3.00/0.99      | sK1 != X2
% 3.00/0.99      | sK2 != X0
% 3.00/0.99      | k1_xboole_0 = X2 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_644,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.00/0.99      | k1_xboole_0 = sK1 ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_643]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_29,negated_conjecture,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.00/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_646,plain,
% 3.00/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_644,c_29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1535,plain,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_12,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1540,plain,
% 3.00/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2570,plain,
% 3.00/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1535,c_1540]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2703,plain,
% 3.00/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_646,c_2570]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_10,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | v1_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1542,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2173,plain,
% 3.00/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1535,c_1542]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_8,plain,
% 3.00/0.99      ( ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v2_funct_1(X0)
% 3.00/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1544,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.00/0.99      | v1_relat_1(X0) != iProver_top
% 3.00/0.99      | v1_funct_1(X0) != iProver_top
% 3.00/0.99      | v2_funct_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4132,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.00/0.99      | v1_funct_1(sK2) != iProver_top
% 3.00/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2173,c_1544]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_31,negated_conjecture,
% 3.00/0.99      ( v1_funct_1(sK2) ),
% 3.00/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_28,negated_conjecture,
% 3.00/0.99      ( v2_funct_1(sK2) ),
% 3.00/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1851,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/0.99      | v1_relat_1(sK2) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1922,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK2)
% 3.00/0.99      | ~ v1_funct_1(sK2)
% 3.00/0.99      | ~ v2_funct_1(sK2)
% 3.00/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4466,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4132,c_31,c_29,c_28,c_1851,c_1922]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_15,plain,
% 3.00/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.00/0.99      | k1_xboole_0 = X1
% 3.00/0.99      | k1_xboole_0 = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_24,plain,
% 3.00/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.00/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_449,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.00/0.99      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.00/0.99      | ~ v1_relat_1(X2)
% 3.00/0.99      | ~ v1_funct_1(X2)
% 3.00/0.99      | X2 != X0
% 3.00/0.99      | k1_relat_1(X2) != X1
% 3.00/0.99      | k1_xboole_0 != X3
% 3.00/0.99      | k1_xboole_0 = X0
% 3.00/0.99      | k1_xboole_0 = X1 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_450,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.00/0.99      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | k1_xboole_0 = X0
% 3.00/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_23,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.00/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_466,plain,
% 3.00/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | k1_xboole_0 = X0
% 3.00/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.00/0.99      inference(forward_subsumption_resolution,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_450,c_23]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1531,plain,
% 3.00/0.99      ( k1_xboole_0 = X0
% 3.00/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.00/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.00/0.99      | v1_relat_1(X0) != iProver_top
% 3.00/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5379,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.00/0.99      | k2_funct_1(sK2) = k1_xboole_0
% 3.00/0.99      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4466,c_1531]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_9,plain,
% 3.00/0.99      ( ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v2_funct_1(X0)
% 3.00/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1543,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.00/0.99      | v1_relat_1(X0) != iProver_top
% 3.00/0.99      | v1_funct_1(X0) != iProver_top
% 3.00/0.99      | v2_funct_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4092,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.00/0.99      | v1_funct_1(sK2) != iProver_top
% 3.00/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2173,c_1543]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_13,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1539,plain,
% 3.00/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2524,plain,
% 3.00/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1535,c_1539]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_27,negated_conjecture,
% 3.00/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.00/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2526,plain,
% 3.00/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2524,c_27]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4103,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.00/0.99      | v1_funct_1(sK2) != iProver_top
% 3.00/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_4092,c_2526]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_32,plain,
% 3.00/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_35,plain,
% 3.00/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4301,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4103,c_32,c_35]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5407,plain,
% 3.00/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 3.00/0.99      | sK1 = k1_xboole_0
% 3.00/0.99      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_5379,c_4301]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_34,plain,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1852,plain,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.00/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1851]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6,plain,
% 3.00/0.99      ( ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.00/0.99      | ~ v2_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1925,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK2)
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.00/0.99      | ~ v1_funct_1(sK2)
% 3.00/0.99      | ~ v2_funct_1(sK2) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1929,plain,
% 3.00/0.99      ( v1_relat_1(sK2) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.00/0.99      | v1_funct_1(sK2) != iProver_top
% 3.00/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7,plain,
% 3.00/0.99      ( ~ v1_relat_1(X0)
% 3.00/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v2_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1924,plain,
% 3.00/0.99      ( v1_relat_1(k2_funct_1(sK2))
% 3.00/0.99      | ~ v1_relat_1(sK2)
% 3.00/0.99      | ~ v1_funct_1(sK2)
% 3.00/0.99      | ~ v2_funct_1(sK2) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1931,plain,
% 3.00/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.00/0.99      | v1_relat_1(sK2) != iProver_top
% 3.00/0.99      | v1_funct_1(sK2) != iProver_top
% 3.00/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6194,plain,
% 3.00/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 3.00/0.99      | sK1 = k1_xboole_0
% 3.00/0.99      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_5407,c_32,c_34,c_35,c_1852,c_1929,c_1931]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6201,plain,
% 3.00/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 3.00/0.99      | sK1 = k1_xboole_0
% 3.00/0.99      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2703,c_6194]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_17,plain,
% 3.00/0.99      ( v1_funct_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.00/0.99      | k1_xboole_0 = X2 ),
% 3.00/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_26,negated_conjecture,
% 3.00/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.00/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_627,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.00/0.99      | k2_funct_1(sK2) != X0
% 3.00/0.99      | sK0 != X2
% 3.00/0.99      | sK1 != X1
% 3.00/0.99      | k1_xboole_0 = X2 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_628,plain,
% 3.00/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.00/0.99      | k1_xboole_0 = sK0 ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_627]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_629,plain,
% 3.00/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.00/0.99      | k1_xboole_0 = sK0
% 3.00/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_786,plain,( X0 = X0 ),theory(equality) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2012,plain,
% 3.00/0.99      ( sK0 = sK0 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_786]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_788,plain,
% 3.00/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.00/0.99      theory(equality) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1995,plain,
% 3.00/0.99      ( ~ r1_tarski(X0,X1)
% 3.00/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.00/0.99      | sK0 != X0
% 3.00/0.99      | k1_xboole_0 != X1 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_788]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2374,plain,
% 3.00/0.99      ( ~ r1_tarski(sK0,X0)
% 3.00/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.00/0.99      | sK0 != sK0
% 3.00/0.99      | k1_xboole_0 != X0 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_1995]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3170,plain,
% 3.00/0.99      ( ~ r1_tarski(sK0,sK0)
% 3.00/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.00/0.99      | sK0 != sK0
% 3.00/0.99      | k1_xboole_0 != sK0 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_2374]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2,plain,
% 3.00/0.99      ( r1_tarski(X0,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3171,plain,
% 3.00/0.99      ( r1_tarski(sK0,sK0) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_20,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1538,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.00/0.99      | v1_relat_1(X0) != iProver_top
% 3.00/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4469,plain,
% 3.00/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4466,c_1538]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4485,plain,
% 3.00/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_4469,c_4301]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4557,plain,
% 3.00/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4485,c_32,c_34,c_35,c_1852,c_1929,c_1931]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4562,plain,
% 3.00/0.99      ( sK1 = k1_xboole_0
% 3.00/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2703,c_4557]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_11,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1541,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3064,plain,
% 3.00/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 3.00/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2570,c_1541]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3765,plain,
% 3.00/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_3064,c_34]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1548,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3771,plain,
% 3.00/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3765,c_1548]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1537,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.00/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.00/0.99      | v1_relat_1(X0) != iProver_top
% 3.00/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4318,plain,
% 3.00/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.00/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_4301,c_1537]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4954,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_4318,c_32,c_34,c_35,c_1852,c_1929,c_1931]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4960,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.00/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_4954,c_4466]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4967,plain,
% 3.00/1.00      ( k1_relset_1(sK1,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
% 3.00/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_4960,c_1540]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4977,plain,
% 3.00/1.00      ( k1_relset_1(sK1,X0,k2_funct_1(sK2)) = sK1
% 3.00/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_4967,c_4301]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4997,plain,
% 3.00/1.00      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3771,c_4977]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6202,plain,
% 3.00/1.00      ( ~ r1_tarski(sK0,k1_xboole_0)
% 3.00/1.00      | k2_funct_1(sK2) = k1_xboole_0
% 3.00/1.00      | sK1 = k1_xboole_0 ),
% 3.00/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6201]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6204,plain,
% 3.00/1.00      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = k1_xboole_0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_6201,c_32,c_34,c_35,c_629,c_1852,c_1929,c_2012,c_3170,
% 3.00/1.00                 c_3171,c_4562,c_4997,c_6202]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6205,plain,
% 3.00/1.00      ( k2_funct_1(sK2) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_6204]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1523,plain,
% 3.00/1.00      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.00/1.00      | k1_xboole_0 = sK0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6224,plain,
% 3.00/1.00      ( k1_relset_1(sK1,sK0,k1_xboole_0) != sK1
% 3.00/1.00      | sK0 = k1_xboole_0
% 3.00/1.00      | sK1 = k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_6205,c_1523]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_787,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1883,plain,
% 3.00/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2011,plain,
% 3.00/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_1883]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7072,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | sK0 = k1_xboole_0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_6224,c_32,c_34,c_35,c_629,c_1852,c_1929,c_2011,c_2012,
% 3.00/1.00                 c_4997]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7073,plain,
% 3.00/1.00      ( sK0 = k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_7072]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7078,plain,
% 3.00/1.00      ( sK0 = k1_xboole_0
% 3.00/1.00      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1549,c_7073]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7080,plain,
% 3.00/1.00      ( sK0 = k1_xboole_0
% 3.00/1.00      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_4960,c_7073]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7176,plain,
% 3.00/1.00      ( sK0 = k1_xboole_0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_7078,c_3771,c_7080]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7198,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7176,c_2570]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_18,plain,
% 3.00/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_563,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.00/1.00      | sK0 != k1_xboole_0
% 3.00/1.00      | sK1 != X1
% 3.00/1.00      | sK2 != X0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_564,plain,
% 3.00/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 3.00/1.00      | sK0 != k1_xboole_0 ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_563]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1526,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 3.00/1.00      | sK0 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7204,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7176,c_1526]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7216,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 3.00/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.00/1.00      inference(equality_resolution_simp,[status(thm)],[c_7204]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7206,plain,
% 3.00/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7176,c_1535]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7219,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
% 3.00/1.00      inference(forward_subsumption_resolution,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_7216,c_7206]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7244,plain,
% 3.00/1.00      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_7198,c_7219]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_8819,plain,
% 3.00/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7244,c_4466]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_9349,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0))) = iProver_top
% 3.00/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_8819,c_1538]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4563,plain,
% 3.00/1.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_4557,c_1548]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4761,plain,
% 3.00/1.00      ( sK1 = k1_xboole_0
% 3.00/1.00      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_2703,c_4563]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_0,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.00/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1551,plain,
% 3.00/1.00      ( X0 = X1
% 3.00/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.00/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5101,plain,
% 3.00/1.00      ( k2_zfmisc_1(sK1,sK0) = k2_funct_1(sK2)
% 3.00/1.00      | sK1 = k1_xboole_0
% 3.00/1.00      | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_4761,c_1551]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_100,plain,
% 3.00/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.00/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_103,plain,
% 3.00/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_107,plain,
% 3.00/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.00/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_789,plain,
% 3.00/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.00/1.00      theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_801,plain,
% 3.00/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_789]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2194,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_790,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.00/1.00      theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1912,plain,
% 3.00/1.00      ( m1_subset_1(X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.00/1.00      | X0 != X2
% 3.00/1.00      | X1 != k1_zfmisc_1(X3) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_790]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2076,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.00      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.00/1.00      | X2 != X0
% 3.00/1.00      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2637,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 3.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != X0
% 3.00/1.00      | k1_zfmisc_1(sK0) != k1_zfmisc_1(X1) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2076]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3396,plain,
% 3.00/1.00      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
% 3.00/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 3.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.00/1.00      | k1_zfmisc_1(sK0) != k1_zfmisc_1(X0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3398,plain,
% 3.00/1.00      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
% 3.00/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 3.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.00/1.00      | k1_zfmisc_1(sK0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_3396]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_673,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/1.00      | ~ v1_relat_1(X0)
% 3.00/1.00      | ~ v1_funct_1(X0)
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relat_1(X0) != sK1
% 3.00/1.00      | k2_funct_1(sK2) != X0
% 3.00/1.00      | sK0 != X1 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_674,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.00/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_673]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_686,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.00/1.00      inference(forward_subsumption_resolution,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_674,c_10]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1521,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_675,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.00/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1950,plain,
% 3.00/1.00      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_1521,c_32,c_34,c_35,c_675,c_1852,c_1929,c_1931]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1951,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_1950]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4305,plain,
% 3.00/1.00      ( sK1 != sK1
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_4301,c_1951]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4306,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.00/1.00      inference(equality_resolution_simp,[status(thm)],[c_4305]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4316,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
% 3.00/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4306]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4496,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.00      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X2))
% 3.00/1.00      | k1_relat_1(sK2) != X0
% 3.00/1.00      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2076]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4498,plain,
% 3.00/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
% 3.00/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.00/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 3.00/1.00      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_4496]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4581,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | sK1 = k1_xboole_0 ),
% 3.00/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4562]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6484,plain,
% 3.00/1.00      ( k1_zfmisc_1(sK0) = k1_zfmisc_1(X0) | sK0 != X0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_789]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6485,plain,
% 3.00/1.00      ( k1_zfmisc_1(sK0) = k1_zfmisc_1(k1_xboole_0)
% 3.00/1.00      | sK0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_6484]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7632,plain,
% 3.00/1.00      ( sK1 = k1_xboole_0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_5101,c_31,c_29,c_28,c_100,c_103,c_107,c_801,c_1851,
% 3.00/1.00                 c_1922,c_2194,c_3398,c_3771,c_4316,c_4498,c_4581,c_6485,
% 3.00/1.00                 c_7080,c_7244]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7649,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7632,c_4301]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_9365,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.00/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_9349,c_7649]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_16,plain,
% 3.00/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_544,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.00/1.00      | k2_funct_1(sK2) != X0
% 3.00/1.00      | sK0 != X1
% 3.00/1.00      | sK1 != k1_xboole_0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_545,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | sK1 != k1_xboole_0 ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_544]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1527,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | sK1 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_546,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | sK1 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2244,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | sK1 != k1_xboole_0
% 3.00/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_1527,c_32,c_34,c_35,c_546,c_1852,c_1929]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2245,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | sK1 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_2244]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7201,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | sK1 != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_7176,c_2245]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_8743,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_7201,c_31,c_29,c_28,c_100,c_103,c_107,c_801,c_1851,
% 3.00/1.00                 c_1922,c_2194,c_3398,c_3771,c_4316,c_4498,c_4581,c_6485,
% 3.00/1.00                 c_7080,c_7244]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2215,plain,
% 3.00/1.00      ( k2_relat_1(sK2) != X0
% 3.00/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != X0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6436,plain,
% 3.00/1.00      ( k2_relat_1(sK2) != sK1
% 3.00/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != sK1 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2215]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4957,plain,
% 3.00/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_4954]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2844,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) != X0
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != X0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4928,plain,
% 3.00/1.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != k2_relat_1(sK2) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2844]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4749,plain,
% 3.00/1.00      ( k2_relat_1(sK2) != X0
% 3.00/1.00      | k1_xboole_0 != X0
% 3.00/1.00      | k1_xboole_0 = k2_relat_1(sK2) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4750,plain,
% 3.00/1.00      ( k2_relat_1(sK2) != k1_xboole_0
% 3.00/1.00      | k1_xboole_0 = k2_relat_1(sK2)
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_4749]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2742,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,X1)
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X2)
% 3.00/1.00      | X2 != X1
% 3.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != X0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_788]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2743,plain,
% 3.00/1.00      ( X0 != X1
% 3.00/1.00      | k2_relat_1(k2_funct_1(sK2)) != X2
% 3.00/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2742]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2745,plain,
% 3.00/1.00      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) = iProver_top
% 3.00/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2743]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2343,plain,
% 3.00/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2344,plain,
% 3.00/1.00      ( sK1 != k1_xboole_0
% 3.00/1.00      | k1_xboole_0 = sK1
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2343]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_518,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.00/1.00      | ~ v1_relat_1(X2)
% 3.00/1.00      | ~ v1_funct_1(X2)
% 3.00/1.00      | X2 != X0
% 3.00/1.00      | X3 != X1
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(X2) != k1_xboole_0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_519,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/1.00      | ~ v1_relat_1(X0)
% 3.00/1.00      | ~ v1_funct_1(X0)
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_518]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_535,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/1.00      | ~ v1_funct_1(X0)
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.00/1.00      inference(forward_subsumption_resolution,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_519,c_10]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2154,plain,
% 3.00/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.00/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
% 3.00/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.00      | k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_535]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2163,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2154]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2165,plain,
% 3.00/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.00/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top
% 3.00/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2163]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1921,plain,
% 3.00/1.00      ( ~ v1_relat_1(sK2)
% 3.00/1.00      | ~ v1_funct_1(sK2)
% 3.00/1.00      | ~ v2_funct_1(sK2)
% 3.00/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_102,plain,
% 3.00/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_104,plain,
% 3.00/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_102]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(contradiction,plain,
% 3.00/1.00      ( $false ),
% 3.00/1.00      inference(minisat,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_9365,c_8819,c_8743,c_7244,c_7080,c_6485,c_6436,c_4957,
% 3.00/1.00                 c_4928,c_4750,c_4581,c_4498,c_4316,c_3771,c_3398,c_2745,
% 3.00/1.00                 c_2526,c_2344,c_2194,c_2165,c_1921,c_1922,c_1931,c_1929,
% 3.00/1.00                 c_1852,c_1851,c_801,c_107,c_104,c_103,c_100,c_35,c_28,
% 3.00/1.00                 c_34,c_29,c_32,c_31]) ).
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  ------                               Statistics
% 3.00/1.00  
% 3.00/1.00  ------ General
% 3.00/1.00  
% 3.00/1.00  abstr_ref_over_cycles:                  0
% 3.00/1.00  abstr_ref_under_cycles:                 0
% 3.00/1.00  gc_basic_clause_elim:                   0
% 3.00/1.00  forced_gc_time:                         0
% 3.00/1.00  parsing_time:                           0.011
% 3.00/1.00  unif_index_cands_time:                  0.
% 3.00/1.00  unif_index_add_time:                    0.
% 3.00/1.00  orderings_time:                         0.
% 3.00/1.00  out_proof_time:                         0.013
% 3.00/1.00  total_time:                             0.275
% 3.00/1.00  num_of_symbols:                         48
% 3.00/1.00  num_of_terms:                           6402
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing
% 3.00/1.00  
% 3.00/1.00  num_of_splits:                          0
% 3.00/1.00  num_of_split_atoms:                     0
% 3.00/1.00  num_of_reused_defs:                     0
% 3.00/1.00  num_eq_ax_congr_red:                    3
% 3.00/1.00  num_of_sem_filtered_clauses:            1
% 3.00/1.00  num_of_subtypes:                        0
% 3.00/1.00  monotx_restored_types:                  0
% 3.00/1.00  sat_num_of_epr_types:                   0
% 3.00/1.00  sat_num_of_non_cyclic_types:            0
% 3.00/1.00  sat_guarded_non_collapsed_types:        0
% 3.00/1.00  num_pure_diseq_elim:                    0
% 3.00/1.00  simp_replaced_by:                       0
% 3.00/1.00  res_preprocessed:                       126
% 3.00/1.00  prep_upred:                             0
% 3.00/1.00  prep_unflattend:                        51
% 3.00/1.00  smt_new_axioms:                         0
% 3.00/1.00  pred_elim_cands:                        6
% 3.00/1.00  pred_elim:                              1
% 3.00/1.00  pred_elim_cl:                           -5
% 3.00/1.00  pred_elim_cycles:                       2
% 3.00/1.00  merged_defs:                            6
% 3.00/1.00  merged_defs_ncl:                        0
% 3.00/1.00  bin_hyper_res:                          6
% 3.00/1.00  prep_cycles:                            3
% 3.00/1.00  pred_elim_time:                         0.009
% 3.00/1.00  splitting_time:                         0.
% 3.00/1.00  sem_filter_time:                        0.
% 3.00/1.00  monotx_time:                            0.001
% 3.00/1.00  subtype_inf_time:                       0.
% 3.00/1.00  
% 3.00/1.00  ------ Problem properties
% 3.00/1.00  
% 3.00/1.00  clauses:                                34
% 3.00/1.00  conjectures:                            4
% 3.00/1.00  epr:                                    4
% 3.00/1.00  horn:                                   28
% 3.00/1.00  ground:                                 13
% 3.00/1.00  unary:                                  5
% 3.00/1.00  binary:                                 7
% 3.00/1.00  lits:                                   111
% 3.00/1.00  lits_eq:                                38
% 3.00/1.00  fd_pure:                                0
% 3.00/1.00  fd_pseudo:                              0
% 3.00/1.00  fd_cond:                                3
% 3.00/1.00  fd_pseudo_cond:                         1
% 3.00/1.00  ac_symbols:                             0
% 3.00/1.00  
% 3.00/1.00  ------ Propositional Solver
% 3.00/1.00  
% 3.00/1.00  prop_solver_calls:                      25
% 3.00/1.00  prop_fast_solver_calls:                 1278
% 3.00/1.00  smt_solver_calls:                       0
% 3.00/1.00  smt_fast_solver_calls:                  0
% 3.00/1.00  prop_num_of_clauses:                    3296
% 3.00/1.00  prop_preprocess_simplified:             7213
% 3.00/1.00  prop_fo_subsumed:                       62
% 3.00/1.00  prop_solver_time:                       0.
% 3.00/1.00  smt_solver_time:                        0.
% 3.00/1.00  smt_fast_solver_time:                   0.
% 3.00/1.00  prop_fast_solver_time:                  0.
% 3.00/1.00  prop_unsat_core_time:                   0.
% 3.00/1.00  
% 3.00/1.00  ------ QBF
% 3.00/1.00  
% 3.00/1.00  qbf_q_res:                              0
% 3.00/1.00  qbf_num_tautologies:                    0
% 3.00/1.00  qbf_prep_cycles:                        0
% 3.00/1.00  
% 3.00/1.00  ------ BMC1
% 3.00/1.00  
% 3.00/1.00  bmc1_current_bound:                     -1
% 3.00/1.00  bmc1_last_solved_bound:                 -1
% 3.00/1.00  bmc1_unsat_core_size:                   -1
% 3.00/1.00  bmc1_unsat_core_parents_size:           -1
% 3.00/1.00  bmc1_merge_next_fun:                    0
% 3.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation
% 3.00/1.00  
% 3.00/1.00  inst_num_of_clauses:                    1043
% 3.00/1.00  inst_num_in_passive:                    338
% 3.00/1.00  inst_num_in_active:                     501
% 3.00/1.00  inst_num_in_unprocessed:                207
% 3.00/1.00  inst_num_of_loops:                      620
% 3.00/1.00  inst_num_of_learning_restarts:          0
% 3.00/1.00  inst_num_moves_active_passive:          115
% 3.00/1.00  inst_lit_activity:                      0
% 3.00/1.00  inst_lit_activity_moves:                0
% 3.00/1.00  inst_num_tautologies:                   0
% 3.00/1.00  inst_num_prop_implied:                  0
% 3.00/1.00  inst_num_existing_simplified:           0
% 3.00/1.00  inst_num_eq_res_simplified:             0
% 3.00/1.00  inst_num_child_elim:                    0
% 3.00/1.00  inst_num_of_dismatching_blockings:      377
% 3.00/1.00  inst_num_of_non_proper_insts:           1130
% 3.00/1.00  inst_num_of_duplicates:                 0
% 3.00/1.00  inst_inst_num_from_inst_to_res:         0
% 3.00/1.00  inst_dismatching_checking_time:         0.
% 3.00/1.00  
% 3.00/1.00  ------ Resolution
% 3.00/1.00  
% 3.00/1.00  res_num_of_clauses:                     0
% 3.00/1.00  res_num_in_passive:                     0
% 3.00/1.00  res_num_in_active:                      0
% 3.00/1.00  res_num_of_loops:                       129
% 3.00/1.00  res_forward_subset_subsumed:            55
% 3.00/1.00  res_backward_subset_subsumed:           12
% 3.00/1.00  res_forward_subsumed:                   0
% 3.00/1.00  res_backward_subsumed:                  0
% 3.00/1.00  res_forward_subsumption_resolution:     6
% 3.00/1.00  res_backward_subsumption_resolution:    0
% 3.00/1.00  res_clause_to_clause_subsumption:       542
% 3.00/1.00  res_orphan_elimination:                 0
% 3.00/1.00  res_tautology_del:                      92
% 3.00/1.00  res_num_eq_res_simplified:              0
% 3.00/1.00  res_num_sel_changes:                    0
% 3.00/1.00  res_moves_from_active_to_pass:          0
% 3.00/1.00  
% 3.00/1.00  ------ Superposition
% 3.00/1.00  
% 3.00/1.00  sup_time_total:                         0.
% 3.00/1.00  sup_time_generating:                    0.
% 3.00/1.00  sup_time_sim_full:                      0.
% 3.00/1.00  sup_time_sim_immed:                     0.
% 3.00/1.00  
% 3.00/1.00  sup_num_of_clauses:                     139
% 3.00/1.00  sup_num_in_active:                      57
% 3.00/1.00  sup_num_in_passive:                     82
% 3.00/1.00  sup_num_of_loops:                       122
% 3.00/1.00  sup_fw_superposition:                   113
% 3.00/1.00  sup_bw_superposition:                   164
% 3.00/1.00  sup_immediate_simplified:               110
% 3.00/1.00  sup_given_eliminated:                   0
% 3.00/1.00  comparisons_done:                       0
% 3.00/1.00  comparisons_avoided:                    25
% 3.00/1.00  
% 3.00/1.00  ------ Simplifications
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  sim_fw_subset_subsumed:                 32
% 3.00/1.00  sim_bw_subset_subsumed:                 31
% 3.00/1.00  sim_fw_subsumed:                        23
% 3.00/1.00  sim_bw_subsumed:                        1
% 3.00/1.00  sim_fw_subsumption_res:                 2
% 3.00/1.00  sim_bw_subsumption_res:                 0
% 3.00/1.00  sim_tautology_del:                      8
% 3.00/1.00  sim_eq_tautology_del:                   10
% 3.00/1.00  sim_eq_res_simp:                        6
% 3.00/1.00  sim_fw_demodulated:                     3
% 3.00/1.00  sim_bw_demodulated:                     61
% 3.00/1.00  sim_light_normalised:                   64
% 3.00/1.00  sim_joinable_taut:                      0
% 3.00/1.00  sim_joinable_simp:                      0
% 3.00/1.00  sim_ac_normalised:                      0
% 3.00/1.00  sim_smt_subsumption:                    0
% 3.00/1.00  
%------------------------------------------------------------------------------
