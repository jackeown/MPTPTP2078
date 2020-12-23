%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:14 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  195 (2443 expanded)
%              Number of clauses        :  131 ( 910 expanded)
%              Number of leaves         :   15 ( 427 expanded)
%              Depth                    :   28
%              Number of atoms          :  538 (9335 expanded)
%              Number of equality atoms :  299 (2128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,
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

fof(f39,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f38])).

fof(f66,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f37,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X1)
      | k2_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0))
      | ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_815,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_283,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ r1_tarski(k2_relat_1(sK1),X1) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_804,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_804])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_143,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_28])).

cnf(c_144,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_143])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_144])).

cnf(c_353,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_353,c_18])).

cnf(c_801,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_983,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_801])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_963,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_965,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_986,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_32,c_965])).

cnf(c_806,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_990,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_986,c_806])).

cnf(c_1325,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_990])).

cnf(c_1326,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1325])).

cnf(c_1414,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_1326])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_813,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,k3_subset_1(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_809,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_160,plain,
    ( r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_10])).

cnf(c_805,plain,
    ( r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_9,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_839,plain,
    ( r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_805,c_9])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_816,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2325,plain,
    ( k3_subset_1(X0,X0) = X0
    | r1_tarski(X0,k3_subset_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_816])).

cnf(c_3343,plain,
    ( k3_subset_1(X0,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_2325])).

cnf(c_812,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_812,c_9])).

cnf(c_3552,plain,
    ( k3_subset_1(X0,X0) = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3343,c_836])).

cnf(c_3560,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_813,c_3552])).

cnf(c_4166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_809])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_79,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7170,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4166,c_60,c_79])).

cnf(c_7171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7170])).

cnf(c_7178,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_7171])).

cnf(c_7603,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7178,c_816])).

cnf(c_929,plain,
    ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_964,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),X0) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_967,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_969,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_20,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_309,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK1) != X0
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_144])).

cnf(c_310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_322,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_310,c_15])).

cnf(c_803,plain,
    ( sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( sK0 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_1040,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_32,c_327,c_965,c_983])).

cnf(c_1044,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1040,c_986])).

cnf(c_1118,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1119,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1205,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1507,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),k1_xboole_0)
    | ~ r1_tarski(sK1,k3_subset_1(X0,X1))
    | r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_1509,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k3_subset_1(X0,X1)) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_1511,plain,
    ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k3_subset_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
    | r1_tarski(sK1,k3_subset_1(X1,X0))
    | ~ r1_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(X1,X0)) = iProver_top
    | r1_xboole_0(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1508])).

cnf(c_1515,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_807,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1642,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_807])).

cnf(c_1741,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1414,c_1642])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_144])).

cnf(c_337,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_802,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_909,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_802,c_7])).

cnf(c_1061,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_1062,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_1086,plain,
    ( k1_relat_1(sK1) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_32,c_965,c_1062])).

cnf(c_1087,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1086])).

cnf(c_1090,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1087,c_986])).

cnf(c_1920,plain,
    ( k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1741,c_1090])).

cnf(c_2006,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2009,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_7921,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7603,c_60,c_929,c_965,c_969,c_990,c_1044,c_1119,c_1414,c_1511,c_1515,c_1920,c_2009])).

cnf(c_814,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2358,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_814])).

cnf(c_2357,plain,
    ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_814])).

cnf(c_3358,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_subset_1(X0,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_814])).

cnf(c_4285,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_3358])).

cnf(c_4660,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_4285])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_817,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1734,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_817])).

cnf(c_4658,plain,
    ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_4285])).

cnf(c_5818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_4658])).

cnf(c_4283,plain,
    ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_3358])).

cnf(c_4609,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_3358])).

cnf(c_5292,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_4609])).

cnf(c_83,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_85,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_4642,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4609])).

cnf(c_5337,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5292,c_85,c_4642])).

cnf(c_2323,plain,
    ( k3_subset_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_816])).

cnf(c_5446,plain,
    ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k1_xboole_0
    | m1_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k1_zfmisc_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | r1_xboole_0(k1_xboole_0,k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_2323])).

cnf(c_808,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6399,plain,
    ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5446,c_1734,c_808,c_836])).

cnf(c_6430,plain,
    ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6399,c_2358])).

cnf(c_7712,plain,
    ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4660,c_58,c_836,c_1734,c_4285,c_5818,c_6430])).

cnf(c_7713,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_7712])).

cnf(c_4615,plain,
    ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
    | r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_2325])).

cnf(c_6401,plain,
    ( k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6399,c_4615])).

cnf(c_6654,plain,
    ( k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6401,c_85])).

cnf(c_6686,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6654,c_839])).

cnf(c_2324,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_816])).

cnf(c_6950,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6686,c_2324])).

cnf(c_7716,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7713,c_3560,c_6950])).

cnf(c_7722,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_7716])).

cnf(c_7926,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7921,c_7722])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 23
% 3.11/0.99  conjectures                             1
% 3.11/0.99  EPR                                     5
% 3.11/0.99  Horn                                    22
% 3.11/0.99  unary                                   11
% 3.11/0.99  binary                                  3
% 3.11/0.99  lits                                    48
% 3.11/0.99  lits eq                                 17
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 1
% 3.11/0.99  fd_pseudo_cond                          2
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99   Resolution empty clause
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(nnf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(flattening,[],[f31])).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.11/0.99    inference(cnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.11/0.99    inference(equality_resolution,[],[f41])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/0.99    inference(nnf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/0.99    inference(flattening,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f48,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.11/0.99    inference(equality_resolution,[],[f48])).
% 3.11/0.99  
% 3.11/0.99  fof(f14,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.11/0.99    inference(ennf_transformation,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.11/0.99    inference(flattening,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f16,conjecture,(
% 3.11/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f17,negated_conjecture,(
% 3.11/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.11/0.99    inference(negated_conjecture,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.11/0.99    inference(flattening,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f66,plain,(
% 3.11/0.99    v1_relat_1(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f15,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(flattening,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f37,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f28])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f69,plain,(
% 3.11/0.99    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f67,plain,(
% 3.11/0.99    v1_funct_1(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f13,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f58,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f68,plain,(
% 3.11/0.99    r1_tarski(k2_relat_1(sK1),sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f45,plain,(
% 3.11/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f23,plain,(
% 3.11/0.99    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/0.99    inference(nnf_transformation,[],[f23])).
% 3.11/0.99  
% 3.11/0.99  fof(f53,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f36])).
% 3.11/0.99  
% 3.11/0.99  fof(f8,axiom,(
% 3.11/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f22,plain,(
% 3.11/0.99    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f8])).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/0.99    inference(nnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f52,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f74,plain,(
% 3.11/0.99    ( ! [X0] : (r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) | ~m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(equality_resolution,[],[f52])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f50,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f7])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f49,plain,(
% 3.11/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.11/0.99    inference(cnf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f10,axiom,(
% 3.11/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f55,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f65,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f75,plain,(
% 3.11/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f65])).
% 3.11/0.99  
% 3.11/0.99  fof(f76,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f75])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f20,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f3])).
% 3.11/0.99  
% 3.11/0.99  fof(f21,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.11/0.99    inference(flattening,[],[f20])).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f63,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f78,plain,(
% 3.11/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f63])).
% 3.11/0.99  
% 3.11/0.99  fof(f47,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.11/0.99    inference(equality_resolution,[],[f47])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f19,plain,(
% 3.11/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.11/0.99    inference(ennf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f71]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_815,plain,
% 3.11/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6,plain,
% 3.11/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_19,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.11/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.11/0.99      | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_29,negated_conjecture,
% 3.11/0.99      ( v1_relat_1(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_282,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.11/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.11/0.99      | sK1 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_283,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/0.99      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 3.11/0.99      | ~ r1_tarski(k2_relat_1(sK1),X1) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_282]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_804,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1161,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_6,c_804]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_23,plain,
% 3.11/0.99      ( v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,negated_conjecture,
% 3.11/0.99      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ v1_funct_1(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_28,negated_conjecture,
% 3.11/0.99      ( v1_funct_1(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_143,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_26,c_28]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_144,negated_conjecture,
% 3.11/0.99      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_143]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_352,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.11/0.99      | k1_relat_1(sK1) != X1
% 3.11/0.99      | sK0 != X2
% 3.11/0.99      | sK1 != X0
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_144]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_353,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 3.11/0.99      | k1_xboole_0 = sK0 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_18,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_361,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | k1_xboole_0 = sK0 ),
% 3.11/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_353,c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_801,plain,
% 3.11/0.99      ( k1_xboole_0 = sK0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_983,plain,
% 3.11/0.99      ( sK0 = k1_xboole_0
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_804,c_801]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_27,negated_conjecture,
% 3.11/0.99      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_32,plain,
% 3.11/0.99      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_963,plain,
% 3.11/0.99      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_965,plain,
% 3.11/0.99      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_986,plain,
% 3.11/0.99      ( sK0 = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_983,c_32,c_965]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_806,plain,
% 3.11/0.99      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_990,plain,
% 3.11/0.99      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_986,c_806]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1325,plain,
% 3.11/0.99      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1161,c_990]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1326,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_1325]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1414,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_815,c_1326]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5,plain,
% 3.11/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_813,plain,
% 3.11/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_14,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.11/0.99      | r1_tarski(X0,k3_subset_1(X1,X2))
% 3.11/0.99      | ~ r1_xboole_0(X0,X2) ),
% 3.11/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_809,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.11/0.99      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top
% 3.11/0.99      | r1_xboole_0(X0,X2) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_11,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
% 3.11/0.99      | r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_10,plain,
% 3.11/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_160,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_11,c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_805,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(X0,k2_subset_1(X0)),k2_subset_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_9,plain,
% 3.11/0.99      ( k2_subset_1(X0) = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_839,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_805,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_816,plain,
% 3.11/0.99      ( X0 = X1
% 3.11/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2325,plain,
% 3.11/0.99      ( k3_subset_1(X0,X0) = X0
% 3.11/0.99      | r1_tarski(X0,k3_subset_1(X0,X0)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_839,c_816]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3343,plain,
% 3.11/0.99      ( k3_subset_1(X0,X0) = X0
% 3.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | r1_xboole_0(X0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_809,c_2325]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_812,plain,
% 3.11/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_836,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_812,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3552,plain,
% 3.11/0.99      ( k3_subset_1(X0,X0) = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3343,c_836]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3560,plain,
% 3.11/0.99      ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_813,c_3552]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4166,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.11/0.99      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3560,c_809]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_15,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_58,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_60,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_58]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_79,plain,
% 3.11/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7170,plain,
% 3.11/0.99      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4166,c_60,c_79]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7171,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_7170]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7178,plain,
% 3.11/0.99      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1414,c_7171]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7603,plain,
% 3.11/0.99      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_7178,c_816]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_929,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_839]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_964,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
% 3.11/0.99      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 3.11/0.99      | ~ r1_tarski(k2_relat_1(sK1),X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_283]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_967,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0))) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_969,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_967]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_20,plain,
% 3.11/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.11/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_309,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.11/0.99      | k1_relat_1(sK1) != X0
% 3.11/0.99      | sK0 != k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_144]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_310,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
% 3.11/0.99      | sK0 != k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK1) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_309]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_322,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | sK0 != k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK1) ),
% 3.11/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_310,c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_803,plain,
% 3.11/0.99      ( sK0 != k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK1)
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_327,plain,
% 3.11/0.99      ( sK0 != k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK1)
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1040,plain,
% 3.11/0.99      ( sK1 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK1)
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_803,c_32,c_327,c_965,c_983]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1044,plain,
% 3.11/0.99      ( k1_relat_1(sK1) = k1_xboole_0
% 3.11/0.99      | sK1 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_1040,c_986]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1118,plain,
% 3.11/0.99      ( ~ r1_tarski(sK1,k1_xboole_0)
% 3.11/0.99      | ~ r1_tarski(k1_xboole_0,sK1)
% 3.11/0.99      | sK1 = k1_xboole_0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1119,plain,
% 3.11/0.99      ( sK1 = k1_xboole_0
% 3.11/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.11/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1205,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.11/0.99      | ~ r1_tarski(sK1,X0)
% 3.11/0.99      | r1_tarski(sK1,k1_xboole_0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1507,plain,
% 3.11/0.99      ( ~ r1_tarski(k3_subset_1(X0,X1),k1_xboole_0)
% 3.11/0.99      | ~ r1_tarski(sK1,k3_subset_1(X0,X1))
% 3.11/0.99      | r1_tarski(sK1,k1_xboole_0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1205]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1509,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(X0,X1),k1_xboole_0) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_subset_1(X0,X1)) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1511,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_subset_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1509]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1508,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
% 3.11/0.99      | r1_tarski(sK1,k3_subset_1(X1,X0))
% 3.11/0.99      | ~ r1_xboole_0(sK1,X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1513,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(X1)) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_subset_1(X1,X0)) = iProver_top
% 3.11/0.99      | r1_xboole_0(sK1,X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1508]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1515,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_subset_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.11/0.99      | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_807,plain,
% 3.11/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1642,plain,
% 3.11/0.99      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 3.11/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_6,c_807]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1741,plain,
% 3.11/0.99      ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1414,c_1642]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,plain,
% 3.11/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_336,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | sK0 != X1
% 3.11/0.99      | sK1 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_144]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_337,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_336]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_802,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7,plain,
% 3.11/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_909,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_802,c_7]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1061,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 3.11/0.99      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 3.11/0.99      | ~ r1_tarski(k2_relat_1(sK1),sK0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_964]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1062,plain,
% 3.11/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) = iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 3.11/0.99      | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1086,plain,
% 3.11/0.99      ( k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_909,c_32,c_965,c_1062]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1087,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_1086]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1090,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_1087,c_986]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1920,plain,
% 3.11/0.99      ( k1_relat_1(sK1) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_1741,c_1090]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2006,plain,
% 3.11/0.99      ( r1_xboole_0(sK1,k1_xboole_0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2009,plain,
% 3.11/0.99      ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7921,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_7603,c_60,c_929,c_965,c_969,c_990,c_1044,c_1119,c_1414,
% 3.11/0.99                 c_1511,c_1515,c_1920,c_2009]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_814,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2358,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(X0,X0),X1) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_839,c_814]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2357,plain,
% 3.11/0.99      ( r1_tarski(k2_relat_1(sK1),X0) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_990,c_814]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3358,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(X0,X0),X2) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2358,c_814]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4285,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2357,c_3358]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4660,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,k3_subset_1(X0,X0)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2358,c_4285]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_0,plain,
% 3.11/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_817,plain,
% 3.11/0.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1734,plain,
% 3.11/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_813,c_817]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4658,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,k3_subset_1(X0,X0)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_839,c_4285]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5818,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
% 3.11/0.99      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_809,c_4658]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4283,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_990,c_3358]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4609,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),X1) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4283,c_3358]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5292,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK1)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_990,c_4609]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_83,plain,
% 3.11/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_85,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_83]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4642,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4609]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5337,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_5292,c_85,c_4642]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2323,plain,
% 3.11/0.99      ( k3_subset_1(X0,X1) = X2
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | r1_tarski(k3_subset_1(X0,X1),X2) != iProver_top
% 3.11/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_809,c_816]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5446,plain,
% 3.11/0.99      ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k1_xboole_0
% 3.11/0.99      | m1_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k1_zfmisc_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 3.11/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 3.11/0.99      | r1_xboole_0(k1_xboole_0,k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_5337,c_2323]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_808,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6399,plain,
% 3.11/0.99      ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k1_xboole_0 ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_5446,c_1734,c_808,c_836]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6430,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X0) != iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_6399,c_2358]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7712,plain,
% 3.11/0.99      ( r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_4660,c_58,c_836,c_1734,c_4285,c_5818,c_6430]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7713,plain,
% 3.11/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.11/1.00      | r1_tarski(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),X1) = iProver_top ),
% 3.11/1.00      inference(renaming,[status(thm)],[c_7712]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_4615,plain,
% 3.11/1.00      ( k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))) = k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
% 3.11/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)),k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_4283,c_2325]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6401,plain,
% 3.11/1.00      ( k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) = k1_xboole_0
% 3.11/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_6399,c_4615]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6654,plain,
% 3.11/1.00      ( k3_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) = k1_xboole_0 ),
% 3.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6401,c_85]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6686,plain,
% 3.11/1.00      ( r1_tarski(k1_xboole_0,k2_relat_1(sK1)) = iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_6654,c_839]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2324,plain,
% 3.11/1.00      ( k2_relat_1(sK1) = k1_xboole_0
% 3.11/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(sK1)) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_990,c_816]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6950,plain,
% 3.11/1.00      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_6686,c_2324]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7716,plain,
% 3.11/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.11/1.00      | r1_tarski(k1_xboole_0,X1) = iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_7713,c_3560,c_6950]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7722,plain,
% 3.11/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_839,c_7716]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7926,plain,
% 3.11/1.00      ( $false ),
% 3.11/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7921,c_7722]) ).
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  ------                               Statistics
% 3.11/1.00  
% 3.11/1.00  ------ General
% 3.11/1.00  
% 3.11/1.00  abstr_ref_over_cycles:                  0
% 3.11/1.00  abstr_ref_under_cycles:                 0
% 3.11/1.00  gc_basic_clause_elim:                   0
% 3.11/1.00  forced_gc_time:                         0
% 3.11/1.00  parsing_time:                           0.012
% 3.11/1.00  unif_index_cands_time:                  0.
% 3.11/1.00  unif_index_add_time:                    0.
% 3.11/1.00  orderings_time:                         0.
% 3.11/1.00  out_proof_time:                         0.013
% 3.11/1.00  total_time:                             0.254
% 3.11/1.00  num_of_symbols:                         47
% 3.11/1.00  num_of_terms:                           7373
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing
% 3.11/1.00  
% 3.11/1.00  num_of_splits:                          0
% 3.11/1.00  num_of_split_atoms:                     0
% 3.11/1.00  num_of_reused_defs:                     0
% 3.11/1.00  num_eq_ax_congr_red:                    11
% 3.11/1.00  num_of_sem_filtered_clauses:            2
% 3.11/1.00  num_of_subtypes:                        0
% 3.11/1.00  monotx_restored_types:                  0
% 3.11/1.00  sat_num_of_epr_types:                   0
% 3.11/1.00  sat_num_of_non_cyclic_types:            0
% 3.11/1.00  sat_guarded_non_collapsed_types:        0
% 3.11/1.00  num_pure_diseq_elim:                    0
% 3.11/1.00  simp_replaced_by:                       0
% 3.11/1.00  res_preprocessed:                       121
% 3.11/1.00  prep_upred:                             0
% 3.11/1.00  prep_unflattend:                        27
% 3.11/1.00  smt_new_axioms:                         0
% 3.11/1.00  pred_elim_cands:                        3
% 3.11/1.00  pred_elim:                              2
% 3.11/1.00  pred_elim_cl:                           5
% 3.11/1.00  pred_elim_cycles:                       4
% 3.11/1.00  merged_defs:                            0
% 3.11/1.00  merged_defs_ncl:                        0
% 3.11/1.00  bin_hyper_res:                          0
% 3.11/1.00  prep_cycles:                            4
% 3.11/1.00  pred_elim_time:                         0.002
% 3.11/1.00  splitting_time:                         0.
% 3.11/1.00  sem_filter_time:                        0.
% 3.11/1.00  monotx_time:                            0.001
% 3.11/1.00  subtype_inf_time:                       0.
% 3.11/1.00  
% 3.11/1.00  ------ Problem properties
% 3.11/1.00  
% 3.11/1.00  clauses:                                23
% 3.11/1.00  conjectures:                            1
% 3.11/1.00  epr:                                    5
% 3.11/1.00  horn:                                   22
% 3.11/1.00  ground:                                 6
% 3.11/1.00  unary:                                  11
% 3.11/1.00  binary:                                 3
% 3.11/1.00  lits:                                   48
% 3.11/1.00  lits_eq:                                17
% 3.11/1.00  fd_pure:                                0
% 3.11/1.00  fd_pseudo:                              0
% 3.11/1.00  fd_cond:                                1
% 3.11/1.00  fd_pseudo_cond:                         2
% 3.11/1.00  ac_symbols:                             0
% 3.11/1.00  
% 3.11/1.00  ------ Propositional Solver
% 3.11/1.00  
% 3.11/1.00  prop_solver_calls:                      29
% 3.11/1.00  prop_fast_solver_calls:                 830
% 3.11/1.00  smt_solver_calls:                       0
% 3.11/1.00  smt_fast_solver_calls:                  0
% 3.11/1.00  prop_num_of_clauses:                    3050
% 3.11/1.00  prop_preprocess_simplified:             7737
% 3.11/1.00  prop_fo_subsumed:                       21
% 3.11/1.00  prop_solver_time:                       0.
% 3.11/1.00  smt_solver_time:                        0.
% 3.11/1.00  smt_fast_solver_time:                   0.
% 3.11/1.00  prop_fast_solver_time:                  0.
% 3.11/1.00  prop_unsat_core_time:                   0.
% 3.11/1.00  
% 3.11/1.00  ------ QBF
% 3.11/1.00  
% 3.11/1.00  qbf_q_res:                              0
% 3.11/1.00  qbf_num_tautologies:                    0
% 3.11/1.00  qbf_prep_cycles:                        0
% 3.11/1.00  
% 3.11/1.00  ------ BMC1
% 3.11/1.00  
% 3.11/1.00  bmc1_current_bound:                     -1
% 3.11/1.00  bmc1_last_solved_bound:                 -1
% 3.11/1.00  bmc1_unsat_core_size:                   -1
% 3.11/1.00  bmc1_unsat_core_parents_size:           -1
% 3.11/1.00  bmc1_merge_next_fun:                    0
% 3.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation
% 3.11/1.00  
% 3.11/1.00  inst_num_of_clauses:                    1034
% 3.11/1.00  inst_num_in_passive:                    158
% 3.11/1.00  inst_num_in_active:                     458
% 3.11/1.00  inst_num_in_unprocessed:                418
% 3.11/1.00  inst_num_of_loops:                      480
% 3.11/1.00  inst_num_of_learning_restarts:          0
% 3.11/1.00  inst_num_moves_active_passive:          19
% 3.11/1.00  inst_lit_activity:                      0
% 3.11/1.00  inst_lit_activity_moves:                0
% 3.11/1.00  inst_num_tautologies:                   0
% 3.11/1.00  inst_num_prop_implied:                  0
% 3.11/1.00  inst_num_existing_simplified:           0
% 3.11/1.00  inst_num_eq_res_simplified:             0
% 3.11/1.00  inst_num_child_elim:                    0
% 3.11/1.00  inst_num_of_dismatching_blockings:      248
% 3.11/1.00  inst_num_of_non_proper_insts:           1136
% 3.11/1.00  inst_num_of_duplicates:                 0
% 3.11/1.00  inst_inst_num_from_inst_to_res:         0
% 3.11/1.00  inst_dismatching_checking_time:         0.
% 3.11/1.00  
% 3.11/1.00  ------ Resolution
% 3.11/1.00  
% 3.11/1.00  res_num_of_clauses:                     0
% 3.11/1.00  res_num_in_passive:                     0
% 3.11/1.00  res_num_in_active:                      0
% 3.11/1.00  res_num_of_loops:                       125
% 3.11/1.00  res_forward_subset_subsumed:            120
% 3.11/1.00  res_backward_subset_subsumed:           0
% 3.11/1.00  res_forward_subsumed:                   0
% 3.11/1.00  res_backward_subsumed:                  0
% 3.11/1.00  res_forward_subsumption_resolution:     2
% 3.11/1.00  res_backward_subsumption_resolution:    0
% 3.11/1.00  res_clause_to_clause_subsumption:       1012
% 3.11/1.00  res_orphan_elimination:                 0
% 3.11/1.00  res_tautology_del:                      121
% 3.11/1.00  res_num_eq_res_simplified:              0
% 3.11/1.00  res_num_sel_changes:                    0
% 3.11/1.00  res_moves_from_active_to_pass:          0
% 3.11/1.00  
% 3.11/1.00  ------ Superposition
% 3.11/1.00  
% 3.11/1.00  sup_time_total:                         0.
% 3.11/1.00  sup_time_generating:                    0.
% 3.11/1.00  sup_time_sim_full:                      0.
% 3.11/1.00  sup_time_sim_immed:                     0.
% 3.11/1.00  
% 3.11/1.00  sup_num_of_clauses:                     130
% 3.11/1.00  sup_num_in_active:                      53
% 3.11/1.00  sup_num_in_passive:                     77
% 3.11/1.00  sup_num_of_loops:                       95
% 3.11/1.00  sup_fw_superposition:                   149
% 3.11/1.00  sup_bw_superposition:                   128
% 3.11/1.00  sup_immediate_simplified:               61
% 3.11/1.00  sup_given_eliminated:                   2
% 3.11/1.00  comparisons_done:                       0
% 3.11/1.00  comparisons_avoided:                    0
% 3.11/1.00  
% 3.11/1.00  ------ Simplifications
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  sim_fw_subset_subsumed:                 32
% 3.11/1.00  sim_bw_subset_subsumed:                 17
% 3.11/1.00  sim_fw_subsumed:                        15
% 3.11/1.00  sim_bw_subsumed:                        2
% 3.11/1.00  sim_fw_subsumption_res:                 5
% 3.11/1.00  sim_bw_subsumption_res:                 0
% 3.11/1.00  sim_tautology_del:                      9
% 3.11/1.00  sim_eq_tautology_del:                   18
% 3.11/1.00  sim_eq_res_simp:                        0
% 3.11/1.00  sim_fw_demodulated:                     7
% 3.11/1.00  sim_bw_demodulated:                     35
% 3.11/1.00  sim_light_normalised:                   24
% 3.11/1.00  sim_joinable_taut:                      0
% 3.11/1.00  sim_joinable_simp:                      0
% 3.11/1.00  sim_ac_normalised:                      0
% 3.11/1.00  sim_smt_subsumption:                    0
% 3.11/1.00  
%------------------------------------------------------------------------------
