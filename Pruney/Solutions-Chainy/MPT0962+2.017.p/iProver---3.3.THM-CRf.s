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
% DateTime   : Thu Dec  3 12:00:11 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  233 (6511 expanded)
%              Number of clauses        :  170 (2507 expanded)
%              Number of leaves         :   20 (1161 expanded)
%              Depth                    :   34
%              Number of atoms          :  698 (24195 expanded)
%              Number of equality atoms :  432 (6554 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f36])).

fof(f62,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f35,plain,(
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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_993,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1003,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_997,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2620,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_997])).

cnf(c_3331,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_993,c_2620])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_995,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_9])).

cnf(c_992,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_2479,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_992])).

cnf(c_8413,plain,
    ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_2479])).

cnf(c_28,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1277,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1221,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ r1_tarski(k2_relat_1(sK1),X1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1335,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_1557,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,X0) = sK1 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1607,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_579,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1152,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_2374,plain,
    ( v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_2375,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2476,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_995])).

cnf(c_4878,plain,
    ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_2476])).

cnf(c_5306,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4878,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375])).

cnf(c_5307,plain,
    ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5306])).

cnf(c_5315,plain,
    ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_5307])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1813,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_992])).

cnf(c_5539,plain,
    ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5315,c_1813])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1002,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2003,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_1813])).

cnf(c_6023,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_2003])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_71,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_73,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_80,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1147,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_1148,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_1150,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_574,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1426,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1427,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_6056,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6023,c_73,c_80,c_81,c_1150,c_1427])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_139,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_26])).

cnf(c_140,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_140])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_399,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_391,c_16])).

cnf(c_989,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1616,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_989])).

cnf(c_1226,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1343,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_573,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1344,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_1623,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1616,c_27,c_25,c_399,c_1277,c_1343,c_1344,c_1557])).

cnf(c_994,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1629,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1623,c_994])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2621,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_997])).

cnf(c_2639,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2621,c_73,c_80,c_81,c_1150,c_1427])).

cnf(c_2640,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2639])).

cnf(c_2648,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k2_relat_1(sK1))) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1629,c_2640])).

cnf(c_6064,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_6056,c_2648])).

cnf(c_6066,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6064,c_13])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_999,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2477,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_1001])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_998,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3850,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_998])).

cnf(c_4242,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375])).

cnf(c_4243,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4242])).

cnf(c_7020,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_4243])).

cnf(c_7026,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7020,c_3331])).

cnf(c_7721,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7026,c_27,c_28,c_25,c_71,c_1277,c_1557,c_1607,c_2375])).

cnf(c_7731,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_7721])).

cnf(c_7944,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7731,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375])).

cnf(c_7945,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7944])).

cnf(c_7956,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_7945])).

cnf(c_7983,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7956,c_3,c_13])).

cnf(c_1315,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1316,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1243,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | X0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1537,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_575,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1375,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1865,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_3511,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | X0 != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_5299,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1)
    | ~ r1_tarski(sK1,sK1)
    | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3511])).

cnf(c_5300,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
    | sK1 != sK1
    | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5299])).

cnf(c_8631,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7983,c_27,c_28,c_25,c_1277,c_1315,c_1316,c_1537,c_1557,c_1607,c_5300])).

cnf(c_8632,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8631])).

cnf(c_8637,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_8632])).

cnf(c_8796,plain,
    ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8413,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375,c_5539,c_8637])).

cnf(c_2788,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_998])).

cnf(c_2839,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2788,c_73,c_80,c_81,c_1150,c_1427])).

cnf(c_2840,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2839])).

cnf(c_3851,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_997])).

cnf(c_4210,plain,
    ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3851,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375])).

cnf(c_4211,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4210])).

cnf(c_4220,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_4211])).

cnf(c_5635,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top
    | k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4220,c_28])).

cnf(c_5636,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5635])).

cnf(c_8801,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8796,c_5636])).

cnf(c_8816,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8801,c_3331])).

cnf(c_1392,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1792,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_3319,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
    | sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_2440,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,X2)
    | X2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_5181,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0)
    | r1_tarski(sK1,X1)
    | X1 != X0
    | sK1 != k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_5198,plain,
    ( X0 != X1
    | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
    | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5181])).

cnf(c_5200,plain,
    ( sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5198])).

cnf(c_5538,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5315,c_1001])).

cnf(c_2789,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_998])).

cnf(c_3458,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2789,c_73,c_80,c_81,c_1150,c_1427])).

cnf(c_3459,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3458])).

cnf(c_7730,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_7721])).

cnf(c_7921,plain,
    ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7730,c_997])).

cnf(c_1000,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8325,plain,
    ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7921,c_1000])).

cnf(c_8332,plain,
    ( k1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_8325])).

cnf(c_8361,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8332,c_4,c_13,c_6056])).

cnf(c_8624,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8361,c_28])).

cnf(c_8625,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8624])).

cnf(c_8832,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8816,c_27,c_28,c_25,c_80,c_81,c_1277,c_1315,c_1537,c_1557,c_1607,c_3319,c_5200,c_5538,c_8361,c_8637])).

cnf(c_7016,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2477])).

cnf(c_8994,plain,
    ( r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8832,c_7016])).

cnf(c_9036,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8994,c_6066])).

cnf(c_13374,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9036,c_27,c_25,c_80,c_81,c_1277,c_1315,c_1537,c_1557,c_1607,c_3319,c_5200,c_5538,c_8637])).

cnf(c_996,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1751,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_996])).

cnf(c_1804,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_1751])).

cnf(c_13391,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_13374,c_1804])).

cnf(c_13535,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13391,c_8832])).

cnf(c_13559,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13535])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1228,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_2873,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1,k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_8146,plain,
    ( ~ m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(X0))
    | m1_subset_1(sK1,k1_zfmisc_1(X1))
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0)
    | sK1 != k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_8147,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
    | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8146])).

cnf(c_8149,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
    | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8147])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_140])).

cnf(c_375,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_990,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1085,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_990,c_4])).

cnf(c_1627,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1623,c_1085])).

cnf(c_1636,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1627,c_3])).

cnf(c_577,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_585,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13559,c_8637,c_8625,c_8149,c_5538,c_5315,c_5200,c_3319,c_1636,c_1607,c_1557,c_1537,c_1315,c_1277,c_585,c_81,c_80,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.05/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.98  
% 4.05/0.98  ------  iProver source info
% 4.05/0.98  
% 4.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.98  git: non_committed_changes: false
% 4.05/0.98  git: last_make_outside_of_git: false
% 4.05/0.98  
% 4.05/0.98  ------ 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options
% 4.05/0.98  
% 4.05/0.98  --out_options                           all
% 4.05/0.98  --tptp_safe_out                         true
% 4.05/0.98  --problem_path                          ""
% 4.05/0.98  --include_path                          ""
% 4.05/0.98  --clausifier                            res/vclausify_rel
% 4.05/0.98  --clausifier_options                    --mode clausify
% 4.05/0.98  --stdin                                 false
% 4.05/0.98  --stats_out                             all
% 4.05/0.98  
% 4.05/0.98  ------ General Options
% 4.05/0.98  
% 4.05/0.98  --fof                                   false
% 4.05/0.98  --time_out_real                         305.
% 4.05/0.98  --time_out_virtual                      -1.
% 4.05/0.98  --symbol_type_check                     false
% 4.05/0.98  --clausify_out                          false
% 4.05/0.98  --sig_cnt_out                           false
% 4.05/0.98  --trig_cnt_out                          false
% 4.05/0.98  --trig_cnt_out_tolerance                1.
% 4.05/0.98  --trig_cnt_out_sk_spl                   false
% 4.05/0.98  --abstr_cl_out                          false
% 4.05/0.98  
% 4.05/0.98  ------ Global Options
% 4.05/0.98  
% 4.05/0.98  --schedule                              default
% 4.05/0.98  --add_important_lit                     false
% 4.05/0.98  --prop_solver_per_cl                    1000
% 4.05/0.98  --min_unsat_core                        false
% 4.05/0.98  --soft_assumptions                      false
% 4.05/0.98  --soft_lemma_size                       3
% 4.05/0.98  --prop_impl_unit_size                   0
% 4.05/0.98  --prop_impl_unit                        []
% 4.05/0.98  --share_sel_clauses                     true
% 4.05/0.98  --reset_solvers                         false
% 4.05/0.98  --bc_imp_inh                            [conj_cone]
% 4.05/0.98  --conj_cone_tolerance                   3.
% 4.05/0.98  --extra_neg_conj                        none
% 4.05/0.98  --large_theory_mode                     true
% 4.05/0.98  --prolific_symb_bound                   200
% 4.05/0.98  --lt_threshold                          2000
% 4.05/0.98  --clause_weak_htbl                      true
% 4.05/0.98  --gc_record_bc_elim                     false
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing Options
% 4.05/0.98  
% 4.05/0.98  --preprocessing_flag                    true
% 4.05/0.98  --time_out_prep_mult                    0.1
% 4.05/0.98  --splitting_mode                        input
% 4.05/0.98  --splitting_grd                         true
% 4.05/0.98  --splitting_cvd                         false
% 4.05/0.98  --splitting_cvd_svl                     false
% 4.05/0.98  --splitting_nvd                         32
% 4.05/0.98  --sub_typing                            true
% 4.05/0.98  --prep_gs_sim                           true
% 4.05/0.98  --prep_unflatten                        true
% 4.05/0.98  --prep_res_sim                          true
% 4.05/0.98  --prep_upred                            true
% 4.05/0.98  --prep_sem_filter                       exhaustive
% 4.05/0.98  --prep_sem_filter_out                   false
% 4.05/0.98  --pred_elim                             true
% 4.05/0.98  --res_sim_input                         true
% 4.05/0.98  --eq_ax_congr_red                       true
% 4.05/0.98  --pure_diseq_elim                       true
% 4.05/0.98  --brand_transform                       false
% 4.05/0.98  --non_eq_to_eq                          false
% 4.05/0.98  --prep_def_merge                        true
% 4.05/0.98  --prep_def_merge_prop_impl              false
% 4.05/0.98  --prep_def_merge_mbd                    true
% 4.05/0.98  --prep_def_merge_tr_red                 false
% 4.05/0.98  --prep_def_merge_tr_cl                  false
% 4.05/0.98  --smt_preprocessing                     true
% 4.05/0.98  --smt_ac_axioms                         fast
% 4.05/0.98  --preprocessed_out                      false
% 4.05/0.98  --preprocessed_stats                    false
% 4.05/0.98  
% 4.05/0.98  ------ Abstraction refinement Options
% 4.05/0.98  
% 4.05/0.98  --abstr_ref                             []
% 4.05/0.98  --abstr_ref_prep                        false
% 4.05/0.98  --abstr_ref_until_sat                   false
% 4.05/0.98  --abstr_ref_sig_restrict                funpre
% 4.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.98  --abstr_ref_under                       []
% 4.05/0.98  
% 4.05/0.98  ------ SAT Options
% 4.05/0.98  
% 4.05/0.98  --sat_mode                              false
% 4.05/0.98  --sat_fm_restart_options                ""
% 4.05/0.98  --sat_gr_def                            false
% 4.05/0.98  --sat_epr_types                         true
% 4.05/0.98  --sat_non_cyclic_types                  false
% 4.05/0.98  --sat_finite_models                     false
% 4.05/0.98  --sat_fm_lemmas                         false
% 4.05/0.98  --sat_fm_prep                           false
% 4.05/0.98  --sat_fm_uc_incr                        true
% 4.05/0.98  --sat_out_model                         small
% 4.05/0.98  --sat_out_clauses                       false
% 4.05/0.98  
% 4.05/0.98  ------ QBF Options
% 4.05/0.98  
% 4.05/0.98  --qbf_mode                              false
% 4.05/0.98  --qbf_elim_univ                         false
% 4.05/0.98  --qbf_dom_inst                          none
% 4.05/0.98  --qbf_dom_pre_inst                      false
% 4.05/0.98  --qbf_sk_in                             false
% 4.05/0.98  --qbf_pred_elim                         true
% 4.05/0.98  --qbf_split                             512
% 4.05/0.98  
% 4.05/0.98  ------ BMC1 Options
% 4.05/0.98  
% 4.05/0.98  --bmc1_incremental                      false
% 4.05/0.98  --bmc1_axioms                           reachable_all
% 4.05/0.98  --bmc1_min_bound                        0
% 4.05/0.98  --bmc1_max_bound                        -1
% 4.05/0.98  --bmc1_max_bound_default                -1
% 4.05/0.98  --bmc1_symbol_reachability              true
% 4.05/0.98  --bmc1_property_lemmas                  false
% 4.05/0.98  --bmc1_k_induction                      false
% 4.05/0.98  --bmc1_non_equiv_states                 false
% 4.05/0.98  --bmc1_deadlock                         false
% 4.05/0.98  --bmc1_ucm                              false
% 4.05/0.98  --bmc1_add_unsat_core                   none
% 4.05/0.98  --bmc1_unsat_core_children              false
% 4.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.98  --bmc1_out_stat                         full
% 4.05/0.98  --bmc1_ground_init                      false
% 4.05/0.98  --bmc1_pre_inst_next_state              false
% 4.05/0.98  --bmc1_pre_inst_state                   false
% 4.05/0.98  --bmc1_pre_inst_reach_state             false
% 4.05/0.98  --bmc1_out_unsat_core                   false
% 4.05/0.98  --bmc1_aig_witness_out                  false
% 4.05/0.98  --bmc1_verbose                          false
% 4.05/0.98  --bmc1_dump_clauses_tptp                false
% 4.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.98  --bmc1_dump_file                        -
% 4.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.98  --bmc1_ucm_extend_mode                  1
% 4.05/0.98  --bmc1_ucm_init_mode                    2
% 4.05/0.98  --bmc1_ucm_cone_mode                    none
% 4.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.98  --bmc1_ucm_relax_model                  4
% 4.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.98  --bmc1_ucm_layered_model                none
% 4.05/0.98  --bmc1_ucm_max_lemma_size               10
% 4.05/0.98  
% 4.05/0.98  ------ AIG Options
% 4.05/0.98  
% 4.05/0.98  --aig_mode                              false
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation Options
% 4.05/0.98  
% 4.05/0.98  --instantiation_flag                    true
% 4.05/0.98  --inst_sos_flag                         false
% 4.05/0.98  --inst_sos_phase                        true
% 4.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel_side                     num_symb
% 4.05/0.98  --inst_solver_per_active                1400
% 4.05/0.98  --inst_solver_calls_frac                1.
% 4.05/0.98  --inst_passive_queue_type               priority_queues
% 4.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.98  --inst_passive_queues_freq              [25;2]
% 4.05/0.98  --inst_dismatching                      true
% 4.05/0.98  --inst_eager_unprocessed_to_passive     true
% 4.05/0.98  --inst_prop_sim_given                   true
% 4.05/0.98  --inst_prop_sim_new                     false
% 4.05/0.98  --inst_subs_new                         false
% 4.05/0.98  --inst_eq_res_simp                      false
% 4.05/0.98  --inst_subs_given                       false
% 4.05/0.98  --inst_orphan_elimination               true
% 4.05/0.98  --inst_learning_loop_flag               true
% 4.05/0.98  --inst_learning_start                   3000
% 4.05/0.98  --inst_learning_factor                  2
% 4.05/0.98  --inst_start_prop_sim_after_learn       3
% 4.05/0.98  --inst_sel_renew                        solver
% 4.05/0.98  --inst_lit_activity_flag                true
% 4.05/0.98  --inst_restr_to_given                   false
% 4.05/0.98  --inst_activity_threshold               500
% 4.05/0.98  --inst_out_proof                        true
% 4.05/0.98  
% 4.05/0.98  ------ Resolution Options
% 4.05/0.98  
% 4.05/0.98  --resolution_flag                       true
% 4.05/0.98  --res_lit_sel                           adaptive
% 4.05/0.98  --res_lit_sel_side                      none
% 4.05/0.98  --res_ordering                          kbo
% 4.05/0.98  --res_to_prop_solver                    active
% 4.05/0.98  --res_prop_simpl_new                    false
% 4.05/0.98  --res_prop_simpl_given                  true
% 4.05/0.98  --res_passive_queue_type                priority_queues
% 4.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.98  --res_passive_queues_freq               [15;5]
% 4.05/0.98  --res_forward_subs                      full
% 4.05/0.98  --res_backward_subs                     full
% 4.05/0.98  --res_forward_subs_resolution           true
% 4.05/0.98  --res_backward_subs_resolution          true
% 4.05/0.98  --res_orphan_elimination                true
% 4.05/0.98  --res_time_limit                        2.
% 4.05/0.98  --res_out_proof                         true
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Options
% 4.05/0.98  
% 4.05/0.98  --superposition_flag                    true
% 4.05/0.98  --sup_passive_queue_type                priority_queues
% 4.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.98  --demod_completeness_check              fast
% 4.05/0.98  --demod_use_ground                      true
% 4.05/0.98  --sup_to_prop_solver                    passive
% 4.05/0.98  --sup_prop_simpl_new                    true
% 4.05/0.98  --sup_prop_simpl_given                  true
% 4.05/0.98  --sup_fun_splitting                     false
% 4.05/0.98  --sup_smt_interval                      50000
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Simplification Setup
% 4.05/0.98  
% 4.05/0.98  --sup_indices_passive                   []
% 4.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_full_bw                           [BwDemod]
% 4.05/0.98  --sup_immed_triv                        [TrivRules]
% 4.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_immed_bw_main                     []
% 4.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/0.98  
% 4.05/0.98  ------ Combination Options
% 4.05/0.98  
% 4.05/0.98  --comb_res_mult                         3
% 4.05/0.98  --comb_sup_mult                         2
% 4.05/0.98  --comb_inst_mult                        10
% 4.05/0.98  
% 4.05/0.98  ------ Debug Options
% 4.05/0.98  
% 4.05/0.98  --dbg_backtrace                         false
% 4.05/0.98  --dbg_dump_prop_clauses                 false
% 4.05/0.98  --dbg_dump_prop_clauses_file            -
% 4.05/0.98  --dbg_out_stat                          false
% 4.05/0.98  ------ Parsing...
% 4.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.98  ------ Proving...
% 4.05/0.98  ------ Problem Properties 
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  clauses                                 21
% 4.05/0.98  conjectures                             2
% 4.05/0.98  EPR                                     3
% 4.05/0.98  Horn                                    20
% 4.05/0.98  unary                                   8
% 4.05/0.98  binary                                  4
% 4.05/0.98  lits                                    49
% 4.05/0.98  lits eq                                 17
% 4.05/0.98  fd_pure                                 0
% 4.05/0.98  fd_pseudo                               0
% 4.05/0.98  fd_cond                                 1
% 4.05/0.98  fd_pseudo_cond                          1
% 4.05/0.98  AC symbols                              0
% 4.05/0.98  
% 4.05/0.98  ------ Schedule dynamic 5 is on 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  ------ 
% 4.05/0.98  Current options:
% 4.05/0.98  ------ 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options
% 4.05/0.98  
% 4.05/0.98  --out_options                           all
% 4.05/0.98  --tptp_safe_out                         true
% 4.05/0.98  --problem_path                          ""
% 4.05/0.98  --include_path                          ""
% 4.05/0.98  --clausifier                            res/vclausify_rel
% 4.05/0.98  --clausifier_options                    --mode clausify
% 4.05/0.98  --stdin                                 false
% 4.05/0.98  --stats_out                             all
% 4.05/0.98  
% 4.05/0.98  ------ General Options
% 4.05/0.98  
% 4.05/0.98  --fof                                   false
% 4.05/0.98  --time_out_real                         305.
% 4.05/0.98  --time_out_virtual                      -1.
% 4.05/0.98  --symbol_type_check                     false
% 4.05/0.98  --clausify_out                          false
% 4.05/0.98  --sig_cnt_out                           false
% 4.05/0.98  --trig_cnt_out                          false
% 4.05/0.98  --trig_cnt_out_tolerance                1.
% 4.05/0.98  --trig_cnt_out_sk_spl                   false
% 4.05/0.98  --abstr_cl_out                          false
% 4.05/0.98  
% 4.05/0.98  ------ Global Options
% 4.05/0.98  
% 4.05/0.98  --schedule                              default
% 4.05/0.98  --add_important_lit                     false
% 4.05/0.98  --prop_solver_per_cl                    1000
% 4.05/0.98  --min_unsat_core                        false
% 4.05/0.98  --soft_assumptions                      false
% 4.05/0.98  --soft_lemma_size                       3
% 4.05/0.98  --prop_impl_unit_size                   0
% 4.05/0.98  --prop_impl_unit                        []
% 4.05/0.98  --share_sel_clauses                     true
% 4.05/0.98  --reset_solvers                         false
% 4.05/0.98  --bc_imp_inh                            [conj_cone]
% 4.05/0.98  --conj_cone_tolerance                   3.
% 4.05/0.98  --extra_neg_conj                        none
% 4.05/0.98  --large_theory_mode                     true
% 4.05/0.98  --prolific_symb_bound                   200
% 4.05/0.98  --lt_threshold                          2000
% 4.05/0.98  --clause_weak_htbl                      true
% 4.05/0.98  --gc_record_bc_elim                     false
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing Options
% 4.05/0.98  
% 4.05/0.98  --preprocessing_flag                    true
% 4.05/0.98  --time_out_prep_mult                    0.1
% 4.05/0.98  --splitting_mode                        input
% 4.05/0.98  --splitting_grd                         true
% 4.05/0.98  --splitting_cvd                         false
% 4.05/0.98  --splitting_cvd_svl                     false
% 4.05/0.98  --splitting_nvd                         32
% 4.05/0.98  --sub_typing                            true
% 4.05/0.98  --prep_gs_sim                           true
% 4.05/0.98  --prep_unflatten                        true
% 4.05/0.98  --prep_res_sim                          true
% 4.05/0.98  --prep_upred                            true
% 4.05/0.98  --prep_sem_filter                       exhaustive
% 4.05/0.98  --prep_sem_filter_out                   false
% 4.05/0.98  --pred_elim                             true
% 4.05/0.98  --res_sim_input                         true
% 4.05/0.98  --eq_ax_congr_red                       true
% 4.05/0.98  --pure_diseq_elim                       true
% 4.05/0.98  --brand_transform                       false
% 4.05/0.98  --non_eq_to_eq                          false
% 4.05/0.98  --prep_def_merge                        true
% 4.05/0.98  --prep_def_merge_prop_impl              false
% 4.05/0.98  --prep_def_merge_mbd                    true
% 4.05/0.98  --prep_def_merge_tr_red                 false
% 4.05/0.98  --prep_def_merge_tr_cl                  false
% 4.05/0.98  --smt_preprocessing                     true
% 4.05/0.98  --smt_ac_axioms                         fast
% 4.05/0.98  --preprocessed_out                      false
% 4.05/0.98  --preprocessed_stats                    false
% 4.05/0.98  
% 4.05/0.98  ------ Abstraction refinement Options
% 4.05/0.98  
% 4.05/0.98  --abstr_ref                             []
% 4.05/0.98  --abstr_ref_prep                        false
% 4.05/0.98  --abstr_ref_until_sat                   false
% 4.05/0.98  --abstr_ref_sig_restrict                funpre
% 4.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.98  --abstr_ref_under                       []
% 4.05/0.98  
% 4.05/0.98  ------ SAT Options
% 4.05/0.98  
% 4.05/0.98  --sat_mode                              false
% 4.05/0.98  --sat_fm_restart_options                ""
% 4.05/0.98  --sat_gr_def                            false
% 4.05/0.98  --sat_epr_types                         true
% 4.05/0.98  --sat_non_cyclic_types                  false
% 4.05/0.98  --sat_finite_models                     false
% 4.05/0.98  --sat_fm_lemmas                         false
% 4.05/0.98  --sat_fm_prep                           false
% 4.05/0.98  --sat_fm_uc_incr                        true
% 4.05/0.98  --sat_out_model                         small
% 4.05/0.98  --sat_out_clauses                       false
% 4.05/0.98  
% 4.05/0.98  ------ QBF Options
% 4.05/0.98  
% 4.05/0.98  --qbf_mode                              false
% 4.05/0.98  --qbf_elim_univ                         false
% 4.05/0.98  --qbf_dom_inst                          none
% 4.05/0.98  --qbf_dom_pre_inst                      false
% 4.05/0.98  --qbf_sk_in                             false
% 4.05/0.98  --qbf_pred_elim                         true
% 4.05/0.98  --qbf_split                             512
% 4.05/0.98  
% 4.05/0.98  ------ BMC1 Options
% 4.05/0.98  
% 4.05/0.98  --bmc1_incremental                      false
% 4.05/0.98  --bmc1_axioms                           reachable_all
% 4.05/0.98  --bmc1_min_bound                        0
% 4.05/0.98  --bmc1_max_bound                        -1
% 4.05/0.98  --bmc1_max_bound_default                -1
% 4.05/0.98  --bmc1_symbol_reachability              true
% 4.05/0.98  --bmc1_property_lemmas                  false
% 4.05/0.98  --bmc1_k_induction                      false
% 4.05/0.98  --bmc1_non_equiv_states                 false
% 4.05/0.98  --bmc1_deadlock                         false
% 4.05/0.98  --bmc1_ucm                              false
% 4.05/0.98  --bmc1_add_unsat_core                   none
% 4.05/0.98  --bmc1_unsat_core_children              false
% 4.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.98  --bmc1_out_stat                         full
% 4.05/0.98  --bmc1_ground_init                      false
% 4.05/0.98  --bmc1_pre_inst_next_state              false
% 4.05/0.98  --bmc1_pre_inst_state                   false
% 4.05/0.98  --bmc1_pre_inst_reach_state             false
% 4.05/0.98  --bmc1_out_unsat_core                   false
% 4.05/0.98  --bmc1_aig_witness_out                  false
% 4.05/0.98  --bmc1_verbose                          false
% 4.05/0.98  --bmc1_dump_clauses_tptp                false
% 4.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.98  --bmc1_dump_file                        -
% 4.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.98  --bmc1_ucm_extend_mode                  1
% 4.05/0.98  --bmc1_ucm_init_mode                    2
% 4.05/0.98  --bmc1_ucm_cone_mode                    none
% 4.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.98  --bmc1_ucm_relax_model                  4
% 4.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.98  --bmc1_ucm_layered_model                none
% 4.05/0.98  --bmc1_ucm_max_lemma_size               10
% 4.05/0.98  
% 4.05/0.98  ------ AIG Options
% 4.05/0.98  
% 4.05/0.98  --aig_mode                              false
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation Options
% 4.05/0.98  
% 4.05/0.98  --instantiation_flag                    true
% 4.05/0.98  --inst_sos_flag                         false
% 4.05/0.98  --inst_sos_phase                        true
% 4.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel_side                     none
% 4.05/0.98  --inst_solver_per_active                1400
% 4.05/0.98  --inst_solver_calls_frac                1.
% 4.05/0.98  --inst_passive_queue_type               priority_queues
% 4.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.98  --inst_passive_queues_freq              [25;2]
% 4.05/0.98  --inst_dismatching                      true
% 4.05/0.98  --inst_eager_unprocessed_to_passive     true
% 4.05/0.98  --inst_prop_sim_given                   true
% 4.05/0.98  --inst_prop_sim_new                     false
% 4.05/0.98  --inst_subs_new                         false
% 4.05/0.98  --inst_eq_res_simp                      false
% 4.05/0.98  --inst_subs_given                       false
% 4.05/0.98  --inst_orphan_elimination               true
% 4.05/0.98  --inst_learning_loop_flag               true
% 4.05/0.98  --inst_learning_start                   3000
% 4.05/0.98  --inst_learning_factor                  2
% 4.05/0.98  --inst_start_prop_sim_after_learn       3
% 4.05/0.98  --inst_sel_renew                        solver
% 4.05/0.98  --inst_lit_activity_flag                true
% 4.05/0.98  --inst_restr_to_given                   false
% 4.05/0.98  --inst_activity_threshold               500
% 4.05/0.98  --inst_out_proof                        true
% 4.05/0.98  
% 4.05/0.98  ------ Resolution Options
% 4.05/0.98  
% 4.05/0.98  --resolution_flag                       false
% 4.05/0.98  --res_lit_sel                           adaptive
% 4.05/0.98  --res_lit_sel_side                      none
% 4.05/0.98  --res_ordering                          kbo
% 4.05/0.98  --res_to_prop_solver                    active
% 4.05/0.98  --res_prop_simpl_new                    false
% 4.05/0.98  --res_prop_simpl_given                  true
% 4.05/0.98  --res_passive_queue_type                priority_queues
% 4.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.98  --res_passive_queues_freq               [15;5]
% 4.05/0.98  --res_forward_subs                      full
% 4.05/0.98  --res_backward_subs                     full
% 4.05/0.98  --res_forward_subs_resolution           true
% 4.05/0.98  --res_backward_subs_resolution          true
% 4.05/0.98  --res_orphan_elimination                true
% 4.05/0.98  --res_time_limit                        2.
% 4.05/0.98  --res_out_proof                         true
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Options
% 4.05/0.98  
% 4.05/0.98  --superposition_flag                    true
% 4.05/0.98  --sup_passive_queue_type                priority_queues
% 4.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.98  --demod_completeness_check              fast
% 4.05/0.98  --demod_use_ground                      true
% 4.05/0.98  --sup_to_prop_solver                    passive
% 4.05/0.98  --sup_prop_simpl_new                    true
% 4.05/0.98  --sup_prop_simpl_given                  true
% 4.05/0.98  --sup_fun_splitting                     false
% 4.05/0.98  --sup_smt_interval                      50000
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Simplification Setup
% 4.05/0.98  
% 4.05/0.98  --sup_indices_passive                   []
% 4.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_full_bw                           [BwDemod]
% 4.05/0.98  --sup_immed_triv                        [TrivRules]
% 4.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_immed_bw_main                     []
% 4.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.05/0.98  
% 4.05/0.98  ------ Combination Options
% 4.05/0.98  
% 4.05/0.98  --comb_res_mult                         3
% 4.05/0.98  --comb_sup_mult                         2
% 4.05/0.98  --comb_inst_mult                        10
% 4.05/0.98  
% 4.05/0.98  ------ Debug Options
% 4.05/0.98  
% 4.05/0.98  --dbg_backtrace                         false
% 4.05/0.98  --dbg_dump_prop_clauses                 false
% 4.05/0.98  --dbg_dump_prop_clauses_file            -
% 4.05/0.98  --dbg_out_stat                          false
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  ------ Proving...
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  % SZS status Theorem for theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  fof(f13,conjecture,(
% 4.05/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f14,negated_conjecture,(
% 4.05/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.05/0.98    inference(negated_conjecture,[],[f13])).
% 4.05/0.98  
% 4.05/0.98  fof(f28,plain,(
% 4.05/0.98    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.05/0.98    inference(ennf_transformation,[],[f14])).
% 4.05/0.98  
% 4.05/0.98  fof(f29,plain,(
% 4.05/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.05/0.98    inference(flattening,[],[f28])).
% 4.05/0.98  
% 4.05/0.98  fof(f36,plain,(
% 4.05/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f37,plain,(
% 4.05/0.98    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 4.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f36])).
% 4.05/0.98  
% 4.05/0.98  fof(f62,plain,(
% 4.05/0.98    v1_relat_1(sK1)),
% 4.05/0.98    inference(cnf_transformation,[],[f37])).
% 4.05/0.98  
% 4.05/0.98  fof(f1,axiom,(
% 4.05/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f30,plain,(
% 4.05/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/0.98    inference(nnf_transformation,[],[f1])).
% 4.05/0.98  
% 4.05/0.98  fof(f31,plain,(
% 4.05/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/0.98    inference(flattening,[],[f30])).
% 4.05/0.98  
% 4.05/0.98  fof(f38,plain,(
% 4.05/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.05/0.98    inference(cnf_transformation,[],[f31])).
% 4.05/0.98  
% 4.05/0.98  fof(f67,plain,(
% 4.05/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.05/0.98    inference(equality_resolution,[],[f38])).
% 4.05/0.98  
% 4.05/0.98  fof(f8,axiom,(
% 4.05/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f20,plain,(
% 4.05/0.98    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.05/0.98    inference(ennf_transformation,[],[f8])).
% 4.05/0.98  
% 4.05/0.98  fof(f21,plain,(
% 4.05/0.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.05/0.98    inference(flattening,[],[f20])).
% 4.05/0.98  
% 4.05/0.98  fof(f52,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f21])).
% 4.05/0.98  
% 4.05/0.98  fof(f11,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f24,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 4.05/0.98    inference(ennf_transformation,[],[f11])).
% 4.05/0.98  
% 4.05/0.98  fof(f25,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 4.05/0.98    inference(flattening,[],[f24])).
% 4.05/0.98  
% 4.05/0.98  fof(f55,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f25])).
% 4.05/0.98  
% 4.05/0.98  fof(f9,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f15,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.05/0.98    inference(pure_predicate_removal,[],[f9])).
% 4.05/0.98  
% 4.05/0.98  fof(f22,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f15])).
% 4.05/0.98  
% 4.05/0.98  fof(f53,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f22])).
% 4.05/0.98  
% 4.05/0.98  fof(f5,axiom,(
% 4.05/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f16,plain,(
% 4.05/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.05/0.98    inference(ennf_transformation,[],[f5])).
% 4.05/0.98  
% 4.05/0.98  fof(f17,plain,(
% 4.05/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.05/0.98    inference(flattening,[],[f16])).
% 4.05/0.98  
% 4.05/0.98  fof(f47,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f17])).
% 4.05/0.98  
% 4.05/0.98  fof(f64,plain,(
% 4.05/0.98    r1_tarski(k2_relat_1(sK1),sK0)),
% 4.05/0.98    inference(cnf_transformation,[],[f37])).
% 4.05/0.98  
% 4.05/0.98  fof(f2,axiom,(
% 4.05/0.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f32,plain,(
% 4.05/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 4.05/0.98    inference(nnf_transformation,[],[f2])).
% 4.05/0.98  
% 4.05/0.98  fof(f33,plain,(
% 4.05/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 4.05/0.98    inference(flattening,[],[f32])).
% 4.05/0.98  
% 4.05/0.98  fof(f42,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 4.05/0.98    inference(cnf_transformation,[],[f33])).
% 4.05/0.98  
% 4.05/0.98  fof(f69,plain,(
% 4.05/0.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 4.05/0.98    inference(equality_resolution,[],[f42])).
% 4.05/0.98  
% 4.05/0.98  fof(f43,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 4.05/0.98    inference(cnf_transformation,[],[f33])).
% 4.05/0.98  
% 4.05/0.98  fof(f68,plain,(
% 4.05/0.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.05/0.98    inference(equality_resolution,[],[f43])).
% 4.05/0.98  
% 4.05/0.98  fof(f3,axiom,(
% 4.05/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f34,plain,(
% 4.05/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.05/0.98    inference(nnf_transformation,[],[f3])).
% 4.05/0.98  
% 4.05/0.98  fof(f45,plain,(
% 4.05/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f34])).
% 4.05/0.98  
% 4.05/0.98  fof(f4,axiom,(
% 4.05/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f46,plain,(
% 4.05/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f4])).
% 4.05/0.98  
% 4.05/0.98  fof(f41,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 4.05/0.98    inference(cnf_transformation,[],[f33])).
% 4.05/0.98  
% 4.05/0.98  fof(f12,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f26,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f12])).
% 4.05/0.98  
% 4.05/0.98  fof(f27,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(flattening,[],[f26])).
% 4.05/0.98  
% 4.05/0.98  fof(f35,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(nnf_transformation,[],[f27])).
% 4.05/0.98  
% 4.05/0.98  fof(f58,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f35])).
% 4.05/0.98  
% 4.05/0.98  fof(f65,plain,(
% 4.05/0.98    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 4.05/0.98    inference(cnf_transformation,[],[f37])).
% 4.05/0.98  
% 4.05/0.98  fof(f63,plain,(
% 4.05/0.98    v1_funct_1(sK1)),
% 4.05/0.98    inference(cnf_transformation,[],[f37])).
% 4.05/0.98  
% 4.05/0.98  fof(f10,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f23,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f10])).
% 4.05/0.98  
% 4.05/0.98  fof(f54,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f23])).
% 4.05/0.98  
% 4.05/0.98  fof(f7,axiom,(
% 4.05/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f50,plain,(
% 4.05/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.05/0.98    inference(cnf_transformation,[],[f7])).
% 4.05/0.98  
% 4.05/0.98  fof(f6,axiom,(
% 4.05/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 4.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f18,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(ennf_transformation,[],[f6])).
% 4.05/0.98  
% 4.05/0.98  fof(f19,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(flattening,[],[f18])).
% 4.05/0.98  
% 4.05/0.98  fof(f49,plain,(
% 4.05/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f19])).
% 4.05/0.98  
% 4.05/0.98  fof(f44,plain,(
% 4.05/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f34])).
% 4.05/0.98  
% 4.05/0.98  fof(f48,plain,(
% 4.05/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f19])).
% 4.05/0.98  
% 4.05/0.98  fof(f40,plain,(
% 4.05/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f31])).
% 4.05/0.98  
% 4.05/0.98  fof(f59,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f35])).
% 4.05/0.98  
% 4.05/0.98  fof(f73,plain,(
% 4.05/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 4.05/0.98    inference(equality_resolution,[],[f59])).
% 4.05/0.98  
% 4.05/0.98  cnf(c_27,negated_conjecture,
% 4.05/0.98      ( v1_relat_1(sK1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_993,plain,
% 4.05/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2,plain,
% 4.05/0.98      ( r1_tarski(X0,X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1003,plain,
% 4.05/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_14,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 4.05/0.98      | ~ v1_relat_1(X1)
% 4.05/0.98      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_997,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 4.05/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2620,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1003,c_997]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3331,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = k1_relat_1(sK1) ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_993,c_2620]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_17,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 4.05/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 4.05/0.98      | ~ v1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_995,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_15,plain,
% 4.05/0.98      ( v4_relat_1(X0,X1)
% 4.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.05/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_9,plain,
% 4.05/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_321,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | ~ v1_relat_1(X0)
% 4.05/0.98      | k7_relat_1(X0,X1) = X0 ),
% 4.05/0.98      inference(resolution,[status(thm)],[c_15,c_9]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_992,plain,
% 4.05/0.98      ( k7_relat_1(X0,X1) = X0
% 4.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2479,plain,
% 4.05/0.98      ( k7_relat_1(X0,X1) = X0
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_995,c_992]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_8413,plain,
% 4.05/0.98      ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_3331,c_2479]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_28,plain,
% 4.05/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_25,negated_conjecture,
% 4.05/0.98      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1277,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1221,plain,
% 4.05/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.05/0.98      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 4.05/0.98      | ~ r1_tarski(k2_relat_1(sK1),X1)
% 4.05/0.98      | ~ v1_relat_1(sK1) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1335,plain,
% 4.05/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
% 4.05/0.98      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 4.05/0.98      | ~ r1_tarski(k2_relat_1(sK1),X0)
% 4.05/0.98      | ~ v1_relat_1(sK1) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1221]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1557,plain,
% 4.05/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 4.05/0.98      | ~ r1_tarski(k2_relat_1(sK1),sK0)
% 4.05/0.98      | ~ v1_relat_1(sK1) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1335]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1211,plain,
% 4.05/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.05/0.98      | ~ v1_relat_1(sK1)
% 4.05/0.98      | k7_relat_1(sK1,X0) = sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_321]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1607,plain,
% 4.05/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | ~ v1_relat_1(sK1)
% 4.05/0.98      | k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1211]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_579,plain,
% 4.05/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 4.05/0.98      theory(equality) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1152,plain,
% 4.05/0.98      ( v1_relat_1(X0) | ~ v1_relat_1(sK1) | X0 != sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_579]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2374,plain,
% 4.05/0.98      ( v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))
% 4.05/0.98      | ~ v1_relat_1(sK1)
% 4.05/0.98      | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1152]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2375,plain,
% 4.05/0.98      ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = iProver_top
% 4.05/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4,plain,
% 4.05/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f69]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2476,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_4,c_995]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4878,plain,
% 4.05/0.98      ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_3331,c_2476]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5306,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 4.05/0.98      | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_4878,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5307,plain,
% 4.05/0.98      ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_5306]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5315,plain,
% 4.05/0.98      ( m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1003,c_5307]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3,plain,
% 4.05/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1813,plain,
% 4.05/0.98      ( k7_relat_1(X0,X1) = X0
% 4.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_3,c_992]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5539,plain,
% 4.05/0.98      ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_5315,c_1813]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_6,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1002,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.05/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2003,plain,
% 4.05/0.98      ( k7_relat_1(X0,X1) = X0
% 4.05/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1002,c_1813]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_6023,plain,
% 4.05/0.98      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 4.05/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1003,c_2003]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_8,plain,
% 4.05/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.05/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_71,plain,
% 4.05/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_73,plain,
% 4.05/0.98      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_71]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5,plain,
% 4.05/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 4.05/0.98      | k1_xboole_0 = X1
% 4.05/0.98      | k1_xboole_0 = X0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_80,plain,
% 4.05/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.05/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_81,plain,
% 4.05/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1147,plain,
% 4.05/0.98      ( v1_relat_1(X0)
% 4.05/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 4.05/0.98      | X0 != k2_zfmisc_1(X1,X2) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_579]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1148,plain,
% 4.05/0.98      ( X0 != k2_zfmisc_1(X1,X2)
% 4.05/0.98      | v1_relat_1(X0) = iProver_top
% 4.05/0.98      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1150,plain,
% 4.05/0.98      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 4.05/0.98      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 4.05/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1148]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_574,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1426,plain,
% 4.05/0.98      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_574]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1427,plain,
% 4.05/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.05/0.98      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 4.05/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1426]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_6056,plain,
% 4.05/0.98      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_6023,c_73,c_80,c_81,c_1150,c_1427]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_21,plain,
% 4.05/0.98      ( v1_funct_2(X0,X1,X2)
% 4.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | k1_relset_1(X1,X2,X0) != X1
% 4.05/0.98      | k1_xboole_0 = X2 ),
% 4.05/0.98      inference(cnf_transformation,[],[f58]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_24,negated_conjecture,
% 4.05/0.98      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 4.05/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | ~ v1_funct_1(sK1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_26,negated_conjecture,
% 4.05/0.98      ( v1_funct_1(sK1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_139,plain,
% 4.05/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_24,c_26]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_140,negated_conjecture,
% 4.05/0.98      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 4.05/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_139]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_390,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | k1_relset_1(X1,X2,X0) != X1
% 4.05/0.98      | k1_relat_1(sK1) != X1
% 4.05/0.98      | sK0 != X2
% 4.05/0.98      | sK1 != X0
% 4.05/0.98      | k1_xboole_0 = X2 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_140]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_391,plain,
% 4.05/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 4.05/0.98      | k1_xboole_0 = sK0 ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_390]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_16,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_399,plain,
% 4.05/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.98      | k1_xboole_0 = sK0 ),
% 4.05/0.98      inference(forward_subsumption_resolution,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_391,c_16]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_989,plain,
% 4.05/0.98      ( k1_xboole_0 = sK0
% 4.05/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1616,plain,
% 4.05/0.98      ( sK0 = k1_xboole_0
% 4.05/0.98      | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1002,c_989]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1226,plain,
% 4.05/0.98      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_574]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1343,plain,
% 4.05/0.98      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1226]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_573,plain,( X0 = X0 ),theory(equality) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1344,plain,
% 4.05/0.98      ( sK0 = sK0 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_573]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1623,plain,
% 4.05/0.98      ( sK0 = k1_xboole_0 ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_1616,c_27,c_25,c_399,c_1277,c_1343,c_1344,c_1557]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_994,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1629,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 4.05/0.98      inference(demodulation,[status(thm)],[c_1623,c_994]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_13,plain,
% 4.05/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.05/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2621,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 4.05/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.05/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_13,c_997]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2639,plain,
% 4.05/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.05/0.98      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_2621,c_73,c_80,c_81,c_1150,c_1427]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2640,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 4.05/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_2639]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2648,plain,
% 4.05/0.98      ( k1_relat_1(k7_relat_1(k1_xboole_0,k2_relat_1(sK1))) = k2_relat_1(sK1) ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1629,c_2640]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_6064,plain,
% 4.05/0.98      ( k1_relat_1(k1_xboole_0) = k2_relat_1(sK1) ),
% 4.05/0.98      inference(demodulation,[status(thm)],[c_6056,c_2648]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_6066,plain,
% 4.05/0.98      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 4.05/0.98      inference(light_normalisation,[status(thm)],[c_6064,c_13]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_10,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,X1)
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 4.05/0.98      | ~ v1_relat_1(X1)
% 4.05/0.98      | ~ v1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_999,plain,
% 4.05/0.98      ( r1_tarski(X0,X1) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top
% 4.05/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1001,plain,
% 4.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.05/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2477,plain,
% 4.05/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_995,c_1001]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_11,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,X1)
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 4.05/0.98      | ~ v1_relat_1(X1)
% 4.05/0.98      | ~ v1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_998,plain,
% 4.05/0.98      ( r1_tarski(X0,X1) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top
% 4.05/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3850,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_3331,c_998]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4242,plain,
% 4.05/0.98      ( v1_relat_1(X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
% 4.05/0.98      | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_3850,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4243,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_4242]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7020,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top
% 4.05/0.98      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2477,c_4243]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7026,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top
% 4.05/0.98      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.05/0.98      inference(light_normalisation,[status(thm)],[c_7020,c_3331]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7721,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),X1) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_7026,c_27,c_28,c_25,c_71,c_1277,c_1557,c_1607,c_2375]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7731,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top
% 4.05/0.98      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_999,c_7721]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7944,plain,
% 4.05/0.98      ( v1_relat_1(X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_7731,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7945,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X1) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) = iProver_top
% 4.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_7944]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7956,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
% 4.05/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_6066,c_7945]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_7983,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top
% 4.05/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.98      inference(light_normalisation,[status(thm)],[c_7956,c_3,c_13]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1315,plain,
% 4.05/0.98      ( r1_tarski(sK1,sK1) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1316,plain,
% 4.05/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_0,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.05/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1243,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | X0 = sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1537,plain,
% 4.05/0.98      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1243]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_575,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.05/0.98      theory(equality) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1375,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_575]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1865,plain,
% 4.05/0.98      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3511,plain,
% 4.05/0.98      ( r1_tarski(X0,sK1)
% 4.05/0.98      | ~ r1_tarski(sK1,sK1)
% 4.05/0.98      | X0 != sK1
% 4.05/0.98      | sK1 != sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1865]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5299,plain,
% 4.05/0.98      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1)
% 4.05/0.98      | ~ r1_tarski(sK1,sK1)
% 4.05/0.98      | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
% 4.05/0.98      | sK1 != sK1 ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_3511]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_5300,plain,
% 4.05/0.98      ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
% 4.05/0.98      | sK1 != sK1
% 4.05/0.98      | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),sK1) = iProver_top
% 4.05/0.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_5299]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_8631,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_7983,c_27,c_28,c_25,c_1277,c_1315,c_1316,c_1537,
% 4.05/0.98                 c_1557,c_1607,c_5300]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_8632,plain,
% 4.05/0.98      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.98      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_8631]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8637,plain,
% 4.05/0.99      ( r1_tarski(k1_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1003,c_8632]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8796,plain,
% 4.05/0.99      ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k1_relat_1(sK1)) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_8413,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375,
% 4.05/0.99                 c_5539,c_8637]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2788,plain,
% 4.05/0.99      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top
% 4.05/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_13,c_998]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2839,plain,
% 4.05/0.99      ( v1_relat_1(X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2788,c_73,c_80,c_81,c_1150,c_1427]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2840,plain,
% 4.05/0.99      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_2839]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3851,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0
% 4.05/0.99      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 4.05/0.99      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3331,c_997]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4210,plain,
% 4.05/0.99      ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 4.05/0.99      | k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0 ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_3851,c_27,c_28,c_25,c_1277,c_1557,c_1607,c_2375]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4211,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) = X0
% 4.05/0.99      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_4210]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4220,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0
% 4.05/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 4.05/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2840,c_4211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5635,plain,
% 4.05/0.99      ( r1_tarski(k1_xboole_0,sK1) != iProver_top
% 4.05/0.99      | k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0 ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_4220,c_28]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5636,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)) = k1_xboole_0
% 4.05/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_5635]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8801,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = k1_xboole_0
% 4.05/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_8796,c_5636]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8816,plain,
% 4.05/0.99      ( k1_relat_1(sK1) = k1_xboole_0
% 4.05/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_8801,c_3331]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1392,plain,
% 4.05/0.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_574]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1792,plain,
% 4.05/0.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1392]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3319,plain,
% 4.05/0.99      ( k7_relat_1(sK1,k1_relat_1(sK1)) != sK1
% 4.05/0.99      | sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.99      | sK1 != sK1 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1792]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2440,plain,
% 4.05/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,X2) | X2 != X1 | sK1 != X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_575]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5181,plain,
% 4.05/0.99      ( ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X0)
% 4.05/0.99      | r1_tarski(sK1,X1)
% 4.05/0.99      | X1 != X0
% 4.05/0.99      | sK1 != k7_relat_1(sK1,k1_relat_1(sK1)) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_2440]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5198,plain,
% 4.05/0.99      ( X0 != X1
% 4.05/0.99      | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.99      | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),X1) != iProver_top
% 4.05/0.99      | r1_tarski(sK1,X0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_5181]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5200,plain,
% 4.05/0.99      ( sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.99      | k1_xboole_0 != k1_xboole_0
% 4.05/0.99      | r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0) != iProver_top
% 4.05/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_5198]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5538,plain,
% 4.05/0.99      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0) = iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_5315,c_1001]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2789,plain,
% 4.05/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top
% 4.05/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_13,c_998]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3458,plain,
% 4.05/0.99      ( v1_relat_1(X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 4.05/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2789,c_73,c_80,c_81,c_1150,c_1427]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3459,plain,
% 4.05/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_3458]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7730,plain,
% 4.05/0.99      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(sK1),k1_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))))) = iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1003,c_7721]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7921,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
% 4.05/0.99      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 4.05/0.99      | v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))))) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7730,c_997]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1000,plain,
% 4.05/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8325,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
% 4.05/0.99      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 4.05/0.99      inference(forward_subsumption_resolution,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_7921,c_1000]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8332,plain,
% 4.05/0.99      ( k1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)))),k1_relat_1(sK1))) = k1_relat_1(sK1)
% 4.05/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 4.05/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3459,c_8325]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8361,plain,
% 4.05/0.99      ( k1_relat_1(sK1) = k1_xboole_0
% 4.05/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 4.05/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_8332,c_4,c_13,c_6056]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8624,plain,
% 4.05/0.99      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 4.05/0.99      | k1_relat_1(sK1) = k1_xboole_0 ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_8361,c_28]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8625,plain,
% 4.05/0.99      ( k1_relat_1(sK1) = k1_xboole_0
% 4.05/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_8624]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8832,plain,
% 4.05/0.99      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_8816,c_27,c_28,c_25,c_80,c_81,c_1277,c_1315,c_1537,
% 4.05/0.99                 c_1557,c_1607,c_3319,c_5200,c_5538,c_8361,c_8637]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7016,plain,
% 4.05/0.99      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 4.05/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 4.05/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_4,c_2477]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8994,plain,
% 4.05/0.99      ( r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 4.05/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.05/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_8832,c_7016]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9036,plain,
% 4.05/0.99      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 4.05/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.05/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_8994,c_6066]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13374,plain,
% 4.05/0.99      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_9036,c_27,c_25,c_80,c_81,c_1277,c_1315,c_1537,c_1557,
% 4.05/0.99                 c_1607,c_3319,c_5200,c_5538,c_8637]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_996,plain,
% 4.05/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1751,plain,
% 4.05/0.99      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 4.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3,c_996]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1804,plain,
% 4.05/0.99      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 4.05/0.99      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1002,c_1751]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13391,plain,
% 4.05/0.99      ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_13374,c_1804]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13535,plain,
% 4.05/0.99      ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_13391,c_8832]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13559,plain,
% 4.05/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_13535]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_578,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1228,plain,
% 4.05/0.99      ( m1_subset_1(X0,X1)
% 4.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 4.05/0.99      | X0 != X2
% 4.05/0.99      | X1 != k1_zfmisc_1(X3) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_578]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1464,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 4.05/0.99      | X2 != X0
% 4.05/0.99      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1228]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2873,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(X2))
% 4.05/0.99      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
% 4.05/0.99      | sK1 != X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1464]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8146,plain,
% 4.05/0.99      ( ~ m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(X0))
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(X1))
% 4.05/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0)
% 4.05/0.99      | sK1 != k7_relat_1(sK1,k1_relat_1(sK1)) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_2873]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8147,plain,
% 4.05/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 4.05/0.99      | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.99      | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(X1)) != iProver_top
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_8146]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8149,plain,
% 4.05/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 4.05/0.99      | sK1 != k7_relat_1(sK1,k1_relat_1(sK1))
% 4.05/0.99      | m1_subset_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_8147]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_20,plain,
% 4.05/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 4.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_374,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.05/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.05/0.99      | sK0 != X1
% 4.05/0.99      | sK1 != X0 ),
% 4.05/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_140]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_375,plain,
% 4.05/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.05/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 4.05/0.99      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0 ),
% 4.05/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_990,plain,
% 4.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1085,plain,
% 4.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_990,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1627,plain,
% 4.05/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1623,c_1085]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1636,plain,
% 4.05/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 4.05/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.05/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1627,c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_577,plain,
% 4.05/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_585,plain,
% 4.05/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 4.05/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_577]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(contradiction,plain,
% 4.05/0.99      ( $false ),
% 4.05/0.99      inference(minisat,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_13559,c_8637,c_8625,c_8149,c_5538,c_5315,c_5200,
% 4.05/0.99                 c_3319,c_1636,c_1607,c_1557,c_1537,c_1315,c_1277,c_585,
% 4.05/0.99                 c_81,c_80,c_25,c_27]) ).
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  ------                               Statistics
% 4.05/0.99  
% 4.05/0.99  ------ General
% 4.05/0.99  
% 4.05/0.99  abstr_ref_over_cycles:                  0
% 4.05/0.99  abstr_ref_under_cycles:                 0
% 4.05/0.99  gc_basic_clause_elim:                   0
% 4.05/0.99  forced_gc_time:                         0
% 4.05/0.99  parsing_time:                           0.012
% 4.05/0.99  unif_index_cands_time:                  0.
% 4.05/0.99  unif_index_add_time:                    0.
% 4.05/0.99  orderings_time:                         0.
% 4.05/0.99  out_proof_time:                         0.02
% 4.05/0.99  total_time:                             0.353
% 4.05/0.99  num_of_symbols:                         46
% 4.05/0.99  num_of_terms:                           9389
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing
% 4.05/0.99  
% 4.05/0.99  num_of_splits:                          0
% 4.05/0.99  num_of_split_atoms:                     0
% 4.05/0.99  num_of_reused_defs:                     0
% 4.05/0.99  num_eq_ax_congr_red:                    10
% 4.05/0.99  num_of_sem_filtered_clauses:            2
% 4.05/0.99  num_of_subtypes:                        0
% 4.05/0.99  monotx_restored_types:                  0
% 4.05/0.99  sat_num_of_epr_types:                   0
% 4.05/0.99  sat_num_of_non_cyclic_types:            0
% 4.05/0.99  sat_guarded_non_collapsed_types:        0
% 4.05/0.99  num_pure_diseq_elim:                    0
% 4.05/0.99  simp_replaced_by:                       0
% 4.05/0.99  res_preprocessed:                       111
% 4.05/0.99  prep_upred:                             0
% 4.05/0.99  prep_unflattend:                        26
% 4.05/0.99  smt_new_axioms:                         0
% 4.05/0.99  pred_elim_cands:                        3
% 4.05/0.99  pred_elim:                              2
% 4.05/0.99  pred_elim_cl:                           5
% 4.05/0.99  pred_elim_cycles:                       4
% 4.05/0.99  merged_defs:                            8
% 4.05/0.99  merged_defs_ncl:                        0
% 4.05/0.99  bin_hyper_res:                          8
% 4.05/0.99  prep_cycles:                            4
% 4.05/0.99  pred_elim_time:                         0.002
% 4.05/0.99  splitting_time:                         0.
% 4.05/0.99  sem_filter_time:                        0.
% 4.05/0.99  monotx_time:                            0.
% 4.05/0.99  subtype_inf_time:                       0.
% 4.05/0.99  
% 4.05/0.99  ------ Problem properties
% 4.05/0.99  
% 4.05/0.99  clauses:                                21
% 4.05/0.99  conjectures:                            2
% 4.05/0.99  epr:                                    3
% 4.05/0.99  horn:                                   20
% 4.05/0.99  ground:                                 7
% 4.05/0.99  unary:                                  8
% 4.05/0.99  binary:                                 4
% 4.05/0.99  lits:                                   49
% 4.05/0.99  lits_eq:                                17
% 4.05/0.99  fd_pure:                                0
% 4.05/0.99  fd_pseudo:                              0
% 4.05/0.99  fd_cond:                                1
% 4.05/0.99  fd_pseudo_cond:                         1
% 4.05/0.99  ac_symbols:                             0
% 4.05/0.99  
% 4.05/0.99  ------ Propositional Solver
% 4.05/0.99  
% 4.05/0.99  prop_solver_calls:                      32
% 4.05/0.99  prop_fast_solver_calls:                 1249
% 4.05/0.99  smt_solver_calls:                       0
% 4.05/0.99  smt_fast_solver_calls:                  0
% 4.05/0.99  prop_num_of_clauses:                    4390
% 4.05/0.99  prop_preprocess_simplified:             7372
% 4.05/0.99  prop_fo_subsumed:                       83
% 4.05/0.99  prop_solver_time:                       0.
% 4.05/0.99  smt_solver_time:                        0.
% 4.05/0.99  smt_fast_solver_time:                   0.
% 4.05/0.99  prop_fast_solver_time:                  0.
% 4.05/0.99  prop_unsat_core_time:                   0.
% 4.05/0.99  
% 4.05/0.99  ------ QBF
% 4.05/0.99  
% 4.05/0.99  qbf_q_res:                              0
% 4.05/0.99  qbf_num_tautologies:                    0
% 4.05/0.99  qbf_prep_cycles:                        0
% 4.05/0.99  
% 4.05/0.99  ------ BMC1
% 4.05/0.99  
% 4.05/0.99  bmc1_current_bound:                     -1
% 4.05/0.99  bmc1_last_solved_bound:                 -1
% 4.05/0.99  bmc1_unsat_core_size:                   -1
% 4.05/0.99  bmc1_unsat_core_parents_size:           -1
% 4.05/0.99  bmc1_merge_next_fun:                    0
% 4.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation
% 4.05/0.99  
% 4.05/0.99  inst_num_of_clauses:                    1077
% 4.05/0.99  inst_num_in_passive:                    627
% 4.05/0.99  inst_num_in_active:                     438
% 4.05/0.99  inst_num_in_unprocessed:                12
% 4.05/0.99  inst_num_of_loops:                      690
% 4.05/0.99  inst_num_of_learning_restarts:          0
% 4.05/0.99  inst_num_moves_active_passive:          246
% 4.05/0.99  inst_lit_activity:                      0
% 4.05/0.99  inst_lit_activity_moves:                0
% 4.05/0.99  inst_num_tautologies:                   0
% 4.05/0.99  inst_num_prop_implied:                  0
% 4.05/0.99  inst_num_existing_simplified:           0
% 4.05/0.99  inst_num_eq_res_simplified:             0
% 4.05/0.99  inst_num_child_elim:                    0
% 4.05/0.99  inst_num_of_dismatching_blockings:      506
% 4.05/0.99  inst_num_of_non_proper_insts:           1536
% 4.05/0.99  inst_num_of_duplicates:                 0
% 4.05/0.99  inst_inst_num_from_inst_to_res:         0
% 4.05/0.99  inst_dismatching_checking_time:         0.
% 4.05/0.99  
% 4.05/0.99  ------ Resolution
% 4.05/0.99  
% 4.05/0.99  res_num_of_clauses:                     0
% 4.05/0.99  res_num_in_passive:                     0
% 4.05/0.99  res_num_in_active:                      0
% 4.05/0.99  res_num_of_loops:                       115
% 4.05/0.99  res_forward_subset_subsumed:            65
% 4.05/0.99  res_backward_subset_subsumed:           6
% 4.05/0.99  res_forward_subsumed:                   0
% 4.05/0.99  res_backward_subsumed:                  0
% 4.05/0.99  res_forward_subsumption_resolution:     1
% 4.05/0.99  res_backward_subsumption_resolution:    0
% 4.05/0.99  res_clause_to_clause_subsumption:       2855
% 4.05/0.99  res_orphan_elimination:                 0
% 4.05/0.99  res_tautology_del:                      91
% 4.05/0.99  res_num_eq_res_simplified:              0
% 4.05/0.99  res_num_sel_changes:                    0
% 4.05/0.99  res_moves_from_active_to_pass:          0
% 4.05/0.99  
% 4.05/0.99  ------ Superposition
% 4.05/0.99  
% 4.05/0.99  sup_time_total:                         0.
% 4.05/0.99  sup_time_generating:                    0.
% 4.05/0.99  sup_time_sim_full:                      0.
% 4.05/0.99  sup_time_sim_immed:                     0.
% 4.05/0.99  
% 4.05/0.99  sup_num_of_clauses:                     250
% 4.05/0.99  sup_num_in_active:                      82
% 4.05/0.99  sup_num_in_passive:                     168
% 4.05/0.99  sup_num_of_loops:                       136
% 4.05/0.99  sup_fw_superposition:                   272
% 4.05/0.99  sup_bw_superposition:                   154
% 4.05/0.99  sup_immediate_simplified:               167
% 4.05/0.99  sup_given_eliminated:                   4
% 4.05/0.99  comparisons_done:                       0
% 4.05/0.99  comparisons_avoided:                    0
% 4.05/0.99  
% 4.05/0.99  ------ Simplifications
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  sim_fw_subset_subsumed:                 31
% 4.05/0.99  sim_bw_subset_subsumed:                 12
% 4.05/0.99  sim_fw_subsumed:                        41
% 4.05/0.99  sim_bw_subsumed:                        15
% 4.05/0.99  sim_fw_subsumption_res:                 3
% 4.05/0.99  sim_bw_subsumption_res:                 0
% 4.05/0.99  sim_tautology_del:                      23
% 4.05/0.99  sim_eq_tautology_del:                   43
% 4.05/0.99  sim_eq_res_simp:                        2
% 4.05/0.99  sim_fw_demodulated:                     31
% 4.05/0.99  sim_bw_demodulated:                     49
% 4.05/0.99  sim_light_normalised:                   124
% 4.05/0.99  sim_joinable_taut:                      0
% 4.05/0.99  sim_joinable_simp:                      0
% 4.05/0.99  sim_ac_normalised:                      0
% 4.05/0.99  sim_smt_subsumption:                    0
% 4.05/0.99  
%------------------------------------------------------------------------------
