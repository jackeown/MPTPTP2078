%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:09 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  160 (2310 expanded)
%              Number of clauses        :   99 ( 949 expanded)
%              Number of leaves         :   16 ( 412 expanded)
%              Depth                    :   26
%              Number of atoms          :  465 (8172 expanded)
%              Number of equality atoms :  224 (1872 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f44,plain,
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

fof(f45,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f44])).

fof(f80,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_10195,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_34])).

cnf(c_203,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_203])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_549,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_541,c_18])).

cnf(c_35,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8357,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_8380,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8357])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8403,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10007,plain,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_35,c_33,c_8380,c_8403])).

cnf(c_10222,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10195,c_10007])).

cnf(c_10196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10436,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10196,c_10207])).

cnf(c_10194,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10203,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10201,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10205,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10212,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10522,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10205,c_10212])).

cnf(c_10653,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) = k1_relat_1(X0)
    | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10201,c_10522])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10206,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11062,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) = k1_relat_1(X0)
    | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10653,c_10206])).

cnf(c_11066,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_11062])).

cnf(c_11103,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_10194,c_11066])).

cnf(c_11120,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),X0)) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11103,c_11062])).

cnf(c_11194,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11120,c_11103])).

cnf(c_10898,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10899,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10898])).

cnf(c_11654,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
    | k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11194,c_10899])).

cnf(c_11655,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11654])).

cnf(c_11663,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),X0) != iProver_top
    | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10436,c_11655])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10202,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10204,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10523,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10204,c_10212])).

cnf(c_10664,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) = k2_relat_1(X1)
    | r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10202,c_10523])).

cnf(c_11228,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) = k2_relat_1(X1)
    | r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10664,c_10206])).

cnf(c_11232,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_11228])).

cnf(c_11403,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_10194,c_11232])).

cnf(c_11668,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11663,c_11103,c_11403])).

cnf(c_8404,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8403])).

cnf(c_12102,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11668,c_8404,c_10899])).

cnf(c_12114,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_10222,c_12102])).

cnf(c_11402,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10206,c_11232])).

cnf(c_12147,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_12114,c_11402])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10200,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13003,plain,
    ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12147,c_10200])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_500,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_501,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_503,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_35])).

cnf(c_687,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k2_relat_1(sK1) != sK0
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_503])).

cnf(c_770,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k2_relat_1(sK1) != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_687])).

cnf(c_10021,plain,
    ( k2_relat_1(sK1) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_35,c_33,c_8380,c_8403])).

cnf(c_10217,plain,
    ( k2_relat_1(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10021,c_10007])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10366,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10198,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13001,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12147,c_10198])).

cnf(c_11102,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10206,c_11066])).

cnf(c_12148,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_12114,c_11102])).

cnf(c_12236,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_12148,c_12114])).

cnf(c_13046,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13001,c_12236])).

cnf(c_12160,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12114,c_10203])).

cnf(c_12600,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12160,c_10206])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10210,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12605,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12600,c_10210])).

cnf(c_13309,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12605,c_35,c_10217,c_10366])).

cnf(c_13319,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13309,c_10523])).

cnf(c_19667,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13003,c_35,c_10217,c_10366,c_13046,c_13319])).

cnf(c_10524,plain,
    ( k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = X0
    | r1_tarski(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_10212])).

cnf(c_10690,plain,
    ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
    | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
    | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10436,c_10524])).

cnf(c_105,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13959,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
    | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
    | k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10690,c_105])).

cnf(c_13960,plain,
    ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
    | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
    | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13959])).

cnf(c_13965,plain,
    ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
    | r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) != iProver_top
    | r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13960,c_11102,c_11402])).

cnf(c_13970,plain,
    ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13965,c_10206,c_10205,c_10204])).

cnf(c_13975,plain,
    ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12114,c_13970])).

cnf(c_19671,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19667,c_13975])).

cnf(c_19673,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19671,c_10206])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.72/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.52  
% 7.72/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.52  
% 7.72/1.52  ------  iProver source info
% 7.72/1.52  
% 7.72/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.52  git: non_committed_changes: false
% 7.72/1.52  git: last_make_outside_of_git: false
% 7.72/1.52  
% 7.72/1.52  ------ 
% 7.72/1.52  ------ Parsing...
% 7.72/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  ------ Proving...
% 7.72/1.52  ------ Problem Properties 
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  clauses                                 33
% 7.72/1.52  conjectures                             2
% 7.72/1.52  EPR                                     4
% 7.72/1.52  Horn                                    28
% 7.72/1.52  unary                                   7
% 7.72/1.52  binary                                  10
% 7.72/1.52  lits                                    83
% 7.72/1.52  lits eq                                 28
% 7.72/1.52  fd_pure                                 0
% 7.72/1.52  fd_pseudo                               0
% 7.72/1.52  fd_cond                                 4
% 7.72/1.52  fd_pseudo_cond                          1
% 7.72/1.52  AC symbols                              0
% 7.72/1.52  
% 7.72/1.52  ------ Input Options Time Limit: Unbounded
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.72/1.52  Current options:
% 7.72/1.52  ------ 
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.72/1.52  
% 7.72/1.52  ------ Proving...
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  % SZS status Theorem for theBenchmark.p
% 7.72/1.52  
% 7.72/1.52   Resolution empty clause
% 7.72/1.52  
% 7.72/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.52  
% 7.72/1.52  fof(f18,conjecture,(
% 7.72/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f19,negated_conjecture,(
% 7.72/1.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.72/1.52    inference(negated_conjecture,[],[f18])).
% 7.72/1.52  
% 7.72/1.52  fof(f37,plain,(
% 7.72/1.52    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.72/1.52    inference(ennf_transformation,[],[f19])).
% 7.72/1.52  
% 7.72/1.52  fof(f38,plain,(
% 7.72/1.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.72/1.52    inference(flattening,[],[f37])).
% 7.72/1.52  
% 7.72/1.52  fof(f44,plain,(
% 7.72/1.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 7.72/1.52    introduced(choice_axiom,[])).
% 7.72/1.52  
% 7.72/1.52  fof(f45,plain,(
% 7.72/1.52    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 7.72/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f44])).
% 7.72/1.52  
% 7.72/1.52  fof(f80,plain,(
% 7.72/1.52    r1_tarski(k2_relat_1(sK1),sK0)),
% 7.72/1.52    inference(cnf_transformation,[],[f45])).
% 7.72/1.52  
% 7.72/1.52  fof(f16,axiom,(
% 7.72/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f33,plain,(
% 7.72/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.52    inference(ennf_transformation,[],[f16])).
% 7.72/1.52  
% 7.72/1.52  fof(f34,plain,(
% 7.72/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.52    inference(flattening,[],[f33])).
% 7.72/1.52  
% 7.72/1.52  fof(f43,plain,(
% 7.72/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.52    inference(nnf_transformation,[],[f34])).
% 7.72/1.52  
% 7.72/1.52  fof(f71,plain,(
% 7.72/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.52    inference(cnf_transformation,[],[f43])).
% 7.72/1.52  
% 7.72/1.52  fof(f81,plain,(
% 7.72/1.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 7.72/1.52    inference(cnf_transformation,[],[f45])).
% 7.72/1.52  
% 7.72/1.52  fof(f79,plain,(
% 7.72/1.52    v1_funct_1(sK1)),
% 7.72/1.52    inference(cnf_transformation,[],[f45])).
% 7.72/1.52  
% 7.72/1.52  fof(f12,axiom,(
% 7.72/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f27,plain,(
% 7.72/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.52    inference(ennf_transformation,[],[f12])).
% 7.72/1.52  
% 7.72/1.52  fof(f64,plain,(
% 7.72/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.52    inference(cnf_transformation,[],[f27])).
% 7.72/1.52  
% 7.72/1.52  fof(f78,plain,(
% 7.72/1.52    v1_relat_1(sK1)),
% 7.72/1.52    inference(cnf_transformation,[],[f45])).
% 7.72/1.52  
% 7.72/1.52  fof(f13,axiom,(
% 7.72/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f28,plain,(
% 7.72/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.72/1.52    inference(ennf_transformation,[],[f13])).
% 7.72/1.52  
% 7.72/1.52  fof(f29,plain,(
% 7.72/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.72/1.52    inference(flattening,[],[f28])).
% 7.72/1.52  
% 7.72/1.52  fof(f65,plain,(
% 7.72/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f29])).
% 7.72/1.52  
% 7.72/1.52  fof(f2,axiom,(
% 7.72/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f39,plain,(
% 7.72/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.72/1.52    inference(nnf_transformation,[],[f2])).
% 7.72/1.52  
% 7.72/1.52  fof(f40,plain,(
% 7.72/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.72/1.52    inference(flattening,[],[f39])).
% 7.72/1.52  
% 7.72/1.52  fof(f47,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.72/1.52    inference(cnf_transformation,[],[f40])).
% 7.72/1.52  
% 7.72/1.52  fof(f83,plain,(
% 7.72/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.72/1.52    inference(equality_resolution,[],[f47])).
% 7.72/1.52  
% 7.72/1.52  fof(f4,axiom,(
% 7.72/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f41,plain,(
% 7.72/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.72/1.52    inference(nnf_transformation,[],[f4])).
% 7.72/1.52  
% 7.72/1.52  fof(f52,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.72/1.52    inference(cnf_transformation,[],[f41])).
% 7.72/1.52  
% 7.72/1.52  fof(f8,axiom,(
% 7.72/1.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f21,plain,(
% 7.72/1.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(ennf_transformation,[],[f8])).
% 7.72/1.52  
% 7.72/1.52  fof(f57,plain,(
% 7.72/1.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f21])).
% 7.72/1.52  
% 7.72/1.52  fof(f9,axiom,(
% 7.72/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f22,plain,(
% 7.72/1.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(ennf_transformation,[],[f9])).
% 7.72/1.52  
% 7.72/1.52  fof(f23,plain,(
% 7.72/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(flattening,[],[f22])).
% 7.72/1.52  
% 7.72/1.52  fof(f58,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f23])).
% 7.72/1.52  
% 7.72/1.52  fof(f6,axiom,(
% 7.72/1.52    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f55,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f6])).
% 7.72/1.52  
% 7.72/1.52  fof(f49,plain,(
% 7.72/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f40])).
% 7.72/1.52  
% 7.72/1.52  fof(f5,axiom,(
% 7.72/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f54,plain,(
% 7.72/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.72/1.52    inference(cnf_transformation,[],[f5])).
% 7.72/1.52  
% 7.72/1.52  fof(f59,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f23])).
% 7.72/1.52  
% 7.72/1.52  fof(f7,axiom,(
% 7.72/1.52    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f56,plain,(
% 7.72/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f7])).
% 7.72/1.52  
% 7.72/1.52  fof(f10,axiom,(
% 7.72/1.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f24,plain,(
% 7.72/1.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(ennf_transformation,[],[f10])).
% 7.72/1.52  
% 7.72/1.52  fof(f25,plain,(
% 7.72/1.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(flattening,[],[f24])).
% 7.72/1.52  
% 7.72/1.52  fof(f61,plain,(
% 7.72/1.52    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f25])).
% 7.72/1.52  
% 7.72/1.52  fof(f17,axiom,(
% 7.72/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f35,plain,(
% 7.72/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.72/1.52    inference(ennf_transformation,[],[f17])).
% 7.72/1.52  
% 7.72/1.52  fof(f36,plain,(
% 7.72/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(flattening,[],[f35])).
% 7.72/1.52  
% 7.72/1.52  fof(f76,plain,(
% 7.72/1.52    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f36])).
% 7.72/1.52  
% 7.72/1.52  fof(f11,axiom,(
% 7.72/1.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f26,plain,(
% 7.72/1.52    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(ennf_transformation,[],[f11])).
% 7.72/1.52  
% 7.72/1.52  fof(f42,plain,(
% 7.72/1.52    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.72/1.52    inference(nnf_transformation,[],[f26])).
% 7.72/1.52  
% 7.72/1.52  fof(f62,plain,(
% 7.72/1.52    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f42])).
% 7.72/1.52  
% 7.72/1.52  fof(f63,plain,(
% 7.72/1.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.72/1.52    inference(cnf_transformation,[],[f42])).
% 7.72/1.52  
% 7.72/1.52  fof(f3,axiom,(
% 7.72/1.52    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 7.72/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.52  
% 7.72/1.52  fof(f20,plain,(
% 7.72/1.52    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 7.72/1.52    inference(ennf_transformation,[],[f3])).
% 7.72/1.52  
% 7.72/1.52  fof(f51,plain,(
% 7.72/1.52    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 7.72/1.52    inference(cnf_transformation,[],[f20])).
% 7.72/1.52  
% 7.72/1.52  cnf(c_33,negated_conjecture,
% 7.72/1.52      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10195,plain,
% 7.72/1.52      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_26,plain,
% 7.72/1.52      ( v1_funct_2(X0,X1,X2)
% 7.72/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.72/1.52      | k1_xboole_0 = X2 ),
% 7.72/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_32,negated_conjecture,
% 7.72/1.52      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 7.72/1.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | ~ v1_funct_1(sK1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_34,negated_conjecture,
% 7.72/1.52      ( v1_funct_1(sK1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_202,plain,
% 7.72/1.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 7.72/1.52      inference(global_propositional_subsumption,[status(thm)],[c_32,c_34]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_203,negated_conjecture,
% 7.72/1.52      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 7.72/1.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 7.72/1.52      inference(renaming,[status(thm)],[c_202]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_540,plain,
% 7.72/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.72/1.52      | k1_relat_1(sK1) != X1
% 7.72/1.52      | sK0 != X2
% 7.72/1.52      | sK1 != X0
% 7.72/1.52      | k1_xboole_0 = X2 ),
% 7.72/1.52      inference(resolution_lifted,[status(thm)],[c_26,c_203]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_541,plain,
% 7.72/1.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 7.72/1.52      | k1_xboole_0 = sK0 ),
% 7.72/1.52      inference(unflattening,[status(thm)],[c_540]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_18,plain,
% 7.72/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_549,plain,
% 7.72/1.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | k1_xboole_0 = sK0 ),
% 7.72/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_541,c_18]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_35,negated_conjecture,
% 7.72/1.52      ( v1_relat_1(sK1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_19,plain,
% 7.72/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.52      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.72/1.52      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.72/1.52      | ~ v1_relat_1(X0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_8357,plain,
% 7.72/1.52      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 7.72/1.52      | ~ r1_tarski(k2_relat_1(sK1),sK0)
% 7.72/1.52      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 7.72/1.52      | ~ v1_relat_1(sK1) ),
% 7.72/1.52      inference(instantiation,[status(thm)],[c_19]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_8380,plain,
% 7.72/1.52      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | ~ r1_tarski(k2_relat_1(sK1),sK0)
% 7.72/1.52      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 7.72/1.52      | ~ v1_relat_1(sK1) ),
% 7.72/1.52      inference(instantiation,[status(thm)],[c_8357]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f83]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_8403,plain,
% 7.72/1.52      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 7.72/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10007,plain,
% 7.72/1.52      ( k1_xboole_0 = sK0 ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_549,c_35,c_33,c_8380,c_8403]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10222,plain,
% 7.72/1.52      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_10195,c_10007]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10196,plain,
% 7.72/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.72/1.52      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_7,plain,
% 7.72/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10207,plain,
% 7.72/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.72/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10436,plain,
% 7.72/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.72/1.52      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10196,c_10207]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10194,plain,
% 7.72/1.52      ( v1_relat_1(sK1) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11,plain,
% 7.72/1.52      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 7.72/1.52      | ~ v1_relat_1(X0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10203,plain,
% 7.72/1.52      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13,plain,
% 7.72/1.52      ( ~ r1_tarski(X0,X1)
% 7.72/1.52      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.72/1.52      | ~ v1_relat_1(X0)
% 7.72/1.52      | ~ v1_relat_1(X1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10201,plain,
% 7.72/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top
% 7.72/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_9,plain,
% 7.72/1.52      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10205,plain,
% 7.72/1.52      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_1,plain,
% 7.72/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.72/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10212,plain,
% 7.72/1.52      ( X0 = X1
% 7.72/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.72/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10522,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 7.72/1.52      | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10205,c_10212]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10653,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) = k1_relat_1(X0)
% 7.72/1.52      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10201,c_10522]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_8,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.72/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10206,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11062,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) = k1_relat_1(X0)
% 7.72/1.52      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) != iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_10653,c_10206]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11066,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k1_relat_1(X0)
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10203,c_11062]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11103,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k1_relat_1(sK1) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10194,c_11066]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11120,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),X0)) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
% 7.72/1.52      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_11103,c_11062]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11194,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
% 7.72/1.52      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_11120,c_11103]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10898,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
% 7.72/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10899,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_10898]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11654,plain,
% 7.72/1.52      ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top
% 7.72/1.52      | k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1) ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_11194,c_10899]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11655,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
% 7.72/1.52      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),k2_zfmisc_1(k1_relat_1(sK1),X0)) != iProver_top ),
% 7.72/1.52      inference(renaming,[status(thm)],[c_11654]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11663,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
% 7.72/1.52      | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),X0) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10436,c_11655]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12,plain,
% 7.72/1.52      ( ~ r1_tarski(X0,X1)
% 7.72/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.72/1.52      | ~ v1_relat_1(X0)
% 7.72/1.52      | ~ v1_relat_1(X1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10202,plain,
% 7.72/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.72/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top
% 7.72/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10,plain,
% 7.72/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 7.72/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10204,plain,
% 7.72/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10523,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 7.72/1.52      | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10204,c_10212]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10664,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) = k2_relat_1(X1)
% 7.72/1.52      | r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top
% 7.72/1.52      | v1_relat_1(X1) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10202,c_10523]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11228,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) = k2_relat_1(X1)
% 7.72/1.52      | r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) != iProver_top
% 7.72/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_10664,c_10206]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11232,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k2_relat_1(X0)
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10203,c_11228]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11403,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k2_relat_1(sK1) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10194,c_11232]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11668,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
% 7.72/1.52      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_11663,c_11103,c_11403]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_8404,plain,
% 7.72/1.52      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_8403]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12102,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),X0)) = k1_relat_1(sK1)
% 7.72/1.52      | r1_tarski(k2_relat_1(sK1),X0) != iProver_top ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_11668,c_8404,c_10899]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12114,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = k1_relat_1(sK1) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10222,c_12102]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11402,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10206,c_11232]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12147,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12114,c_11402]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_14,plain,
% 7.72/1.52      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.72/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10200,plain,
% 7.72/1.52      ( k2_relat_1(X0) != k1_xboole_0
% 7.72/1.52      | k1_xboole_0 = X0
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13003,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = k1_xboole_0
% 7.72/1.52      | k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12147,c_10200]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_30,plain,
% 7.72/1.52      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.72/1.52      | ~ v1_funct_1(X0)
% 7.72/1.52      | ~ v1_relat_1(X0) ),
% 7.72/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_500,plain,
% 7.72/1.52      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.72/1.52      | ~ v1_relat_1(X0)
% 7.72/1.52      | sK1 != X0 ),
% 7.72/1.52      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_501,plain,
% 7.72/1.52      ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~ v1_relat_1(sK1) ),
% 7.72/1.52      inference(unflattening,[status(thm)],[c_500]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_503,plain,
% 7.72/1.52      ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 7.72/1.52      inference(global_propositional_subsumption,[status(thm)],[c_501,c_35]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_687,plain,
% 7.72/1.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | k2_relat_1(sK1) != sK0
% 7.72/1.52      | k1_relat_1(sK1) != k1_relat_1(sK1)
% 7.72/1.52      | sK1 != sK1 ),
% 7.72/1.52      inference(resolution_lifted,[status(thm)],[c_203,c_503]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_770,plain,
% 7.72/1.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 7.72/1.52      | k2_relat_1(sK1) != sK0 ),
% 7.72/1.52      inference(equality_resolution_simp,[status(thm)],[c_687]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10021,plain,
% 7.72/1.52      ( k2_relat_1(sK1) != sK0 ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_770,c_35,c_33,c_8380,c_8403]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10217,plain,
% 7.72/1.52      ( k2_relat_1(sK1) != k1_xboole_0 ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_10021,c_10007]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_17,plain,
% 7.72/1.52      ( ~ v1_relat_1(X0)
% 7.72/1.52      | k2_relat_1(X0) = k1_xboole_0
% 7.72/1.52      | k1_relat_1(X0) != k1_xboole_0 ),
% 7.72/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10366,plain,
% 7.72/1.52      ( ~ v1_relat_1(sK1)
% 7.72/1.52      | k2_relat_1(sK1) = k1_xboole_0
% 7.72/1.52      | k1_relat_1(sK1) != k1_xboole_0 ),
% 7.72/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_16,plain,
% 7.72/1.52      ( ~ v1_relat_1(X0)
% 7.72/1.52      | k2_relat_1(X0) != k1_xboole_0
% 7.72/1.52      | k1_relat_1(X0) = k1_xboole_0 ),
% 7.72/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10198,plain,
% 7.72/1.52      ( k2_relat_1(X0) != k1_xboole_0
% 7.72/1.52      | k1_relat_1(X0) = k1_xboole_0
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13001,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
% 7.72/1.52      | k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_xboole_0
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12147,c_10198]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_11102,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10206,c_11066]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12148,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12114,c_11102]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12236,plain,
% 7.72/1.52      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = k1_relat_1(sK1) ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_12148,c_12114]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13046,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != k1_xboole_0
% 7.72/1.52      | k1_relat_1(sK1) = k1_xboole_0
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
% 7.72/1.52      inference(demodulation,[status(thm)],[c_13001,c_12236]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12160,plain,
% 7.72/1.52      ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12114,c_10203]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12600,plain,
% 7.72/1.52      ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) = iProver_top ),
% 7.72/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_12160,c_10206]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_4,plain,
% 7.72/1.52      ( r1_tarski(X0,X1)
% 7.72/1.52      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
% 7.72/1.52      | k1_xboole_0 = X2 ),
% 7.72/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10210,plain,
% 7.72/1.52      ( k1_xboole_0 = X0
% 7.72/1.52      | r1_tarski(X1,X2) = iProver_top
% 7.72/1.52      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_12605,plain,
% 7.72/1.52      ( k1_relat_1(sK1) = k1_xboole_0
% 7.72/1.52      | r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12600,c_10210]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13309,plain,
% 7.72/1.52      ( r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = iProver_top ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_12605,c_35,c_10217,c_10366]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13319,plain,
% 7.72/1.52      ( k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = k1_xboole_0 ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_13309,c_10523]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_19667,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))) != iProver_top ),
% 7.72/1.52      inference(global_propositional_subsumption,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_13003,c_35,c_10217,c_10366,c_13046,c_13319]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10524,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = X0
% 7.72/1.52      | r1_tarski(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)),X0) != iProver_top
% 7.72/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10203,c_10212]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_10690,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
% 7.72/1.52      | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_10436,c_10524]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_105,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.72/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13959,plain,
% 7.72/1.52      ( r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
% 7.72/1.52      | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
% 7.72/1.52      | k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 7.72/1.52      inference(global_propositional_subsumption,[status(thm)],[c_10690,c_105]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13960,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
% 7.72/1.52      | r1_tarski(k2_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))),X0) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 7.72/1.52      inference(renaming,[status(thm)],[c_13959]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13965,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1)
% 7.72/1.52      | r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) != iProver_top
% 7.72/1.52      | r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) != iProver_top
% 7.72/1.52      | v1_relat_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_13960,c_11102,c_11402]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13970,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) = k2_zfmisc_1(X0,X1) ),
% 7.72/1.52      inference(forward_subsumption_resolution,
% 7.72/1.52                [status(thm)],
% 7.72/1.52                [c_13965,c_10206,c_10205,c_10204]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_13975,plain,
% 7.72/1.52      ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) = k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0) ),
% 7.72/1.52      inference(superposition,[status(thm)],[c_12114,c_13970]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_19671,plain,
% 7.72/1.52      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) != iProver_top ),
% 7.72/1.52      inference(light_normalisation,[status(thm)],[c_19667,c_13975]) ).
% 7.72/1.52  
% 7.72/1.52  cnf(c_19673,plain,
% 7.72/1.52      ( $false ),
% 7.72/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_19671,c_10206]) ).
% 7.72/1.52  
% 7.72/1.52  
% 7.72/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.52  
% 7.72/1.52  ------                               Statistics
% 7.72/1.52  
% 7.72/1.52  ------ Selected
% 7.72/1.52  
% 7.72/1.52  total_time:                             0.781
% 7.72/1.52  
%------------------------------------------------------------------------------
