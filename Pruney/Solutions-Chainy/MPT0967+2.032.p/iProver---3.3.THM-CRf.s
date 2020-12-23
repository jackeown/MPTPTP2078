%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:43 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  164 (2584 expanded)
%              Number of clauses        :  101 ( 961 expanded)
%              Number of leaves         :   16 ( 490 expanded)
%              Depth                    :   25
%              Number of atoms          :  488 (13673 expanded)
%              Number of equality atoms :  235 (4002 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f40])).

fof(f69,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_536,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_538,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_29])).

cnf(c_1311,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1314,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2792,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1311,c_1314])).

cnf(c_3061,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_538,c_2792])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1312,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1319,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1317,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1316,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_385,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | X3 != X0
    | k1_zfmisc_1(X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_371])).

cnf(c_386,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1310,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_2664,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1310])).

cnf(c_5314,plain,
    ( m1_subset_1(sK4,X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_2664])).

cnf(c_5622,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK1,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_5314])).

cnf(c_5809,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_5622])).

cnf(c_6094,plain,
    ( k1_relset_1(sK1,X0,sK4) = k1_relat_1(sK4)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5809,c_1314])).

cnf(c_7196,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1312,c_6094])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_161,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_31])).

cnf(c_162,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_162])).

cnf(c_523,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1305,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_7200,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7196,c_1305])).

cnf(c_35,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1506,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1507,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_412,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_162])).

cnf(c_413,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1309,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1443,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1309,c_5])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_30])).

cnf(c_557,plain,
    ( sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1512,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK3,sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_810,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1585,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_1606,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_1794,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1837,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_812,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1595,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,sK2)
    | sK2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1855,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_1857,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 != sK2
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_1941,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1443,c_28,c_557,c_1512,c_1585,c_1606,c_1794,c_1837,c_1857])).

cnf(c_1942,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1941])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK3 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1942])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2151,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1315])).

cnf(c_2167,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2151])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1553,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1911,plain,
    ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK4,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_3155,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_3156,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3155])).

cnf(c_3465,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3466,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3465])).

cnf(c_7368,plain,
    ( k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7200,c_28,c_35,c_1506,c_1507,c_1943,c_2151,c_2167,c_3155,c_3156,c_3465,c_3466])).

cnf(c_7371,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3061,c_7368])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7403,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7371,c_27])).

cnf(c_7404,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7403])).

cnf(c_7612,plain,
    ( k1_relat_1(sK4) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7404,c_7368])).

cnf(c_7395,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_7371,c_2792])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1306,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1412,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1306,c_6])).

cnf(c_7398,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7371,c_1412])).

cnf(c_7412,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7398,c_7404])).

cnf(c_7413,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7412])).

cnf(c_7401,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7371,c_1311])).

cnf(c_7408,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7401,c_7404])).

cnf(c_7410,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7408,c_6])).

cnf(c_7416,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7413,c_7410])).

cnf(c_7423,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7395,c_7404,c_7416])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7612,c_7423])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 21:08:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.25/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.99  
% 3.25/0.99  ------  iProver source info
% 3.25/0.99  
% 3.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.99  git: non_committed_changes: false
% 3.25/0.99  git: last_make_outside_of_git: false
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     num_symb
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       true
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  ------ Parsing...
% 3.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.99  ------ Proving...
% 3.25/0.99  ------ Problem Properties 
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  clauses                                 29
% 3.25/0.99  conjectures                             3
% 3.25/0.99  EPR                                     6
% 3.25/0.99  Horn                                    24
% 3.25/0.99  unary                                   8
% 3.25/0.99  binary                                  12
% 3.25/0.99  lits                                    63
% 3.25/0.99  lits eq                                 30
% 3.25/0.99  fd_pure                                 0
% 3.25/0.99  fd_pseudo                               0
% 3.25/0.99  fd_cond                                 2
% 3.25/0.99  fd_pseudo_cond                          1
% 3.25/0.99  AC symbols                              0
% 3.25/0.99  
% 3.25/0.99  ------ Schedule dynamic 5 is on 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  Current options:
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     none
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       false
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ Proving...
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS status Theorem for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  fof(f12,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f28,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f12])).
% 3.25/0.99  
% 3.25/0.99  fof(f29,plain,(
% 3.25/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(flattening,[],[f28])).
% 3.25/0.99  
% 3.25/0.99  fof(f37,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(nnf_transformation,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  fof(f59,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f14,conjecture,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f15,negated_conjecture,(
% 3.25/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.25/0.99    inference(negated_conjecture,[],[f14])).
% 3.25/0.99  
% 3.25/0.99  fof(f30,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.25/0.99    inference(ennf_transformation,[],[f15])).
% 3.25/0.99  
% 3.25/0.99  fof(f31,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.25/0.99    inference(flattening,[],[f30])).
% 3.25/0.99  
% 3.25/0.99  fof(f40,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f41,plain,(
% 3.25/0.99    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f69,plain,(
% 3.25/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f70,plain,(
% 3.25/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.25/0.99    inference(cnf_transformation,[],[f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f11,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f27,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f11])).
% 3.25/0.99  
% 3.25/0.99  fof(f58,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f27])).
% 3.25/0.99  
% 3.25/0.99  fof(f71,plain,(
% 3.25/0.99    r1_tarski(sK2,sK3)),
% 3.25/0.99    inference(cnf_transformation,[],[f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f5,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f21,plain,(
% 3.25/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f5])).
% 3.25/0.99  
% 3.25/0.99  fof(f51,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f21])).
% 3.25/0.99  
% 3.25/0.99  fof(f6,axiom,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f22,plain,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f6])).
% 3.25/0.99  
% 3.25/0.99  fof(f52,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f22])).
% 3.25/0.99  
% 3.25/0.99  fof(f9,axiom,(
% 3.25/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f36,plain,(
% 3.25/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.25/0.99    inference(nnf_transformation,[],[f9])).
% 3.25/0.99  
% 3.25/0.99  fof(f56,plain,(
% 3.25/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f36])).
% 3.25/0.99  
% 3.25/0.99  fof(f10,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f25,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.25/0.99    inference(ennf_transformation,[],[f10])).
% 3.25/0.99  
% 3.25/0.99  fof(f26,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.25/0.99    inference(flattening,[],[f25])).
% 3.25/0.99  
% 3.25/0.99  fof(f57,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f7,axiom,(
% 3.25/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f53,plain,(
% 3.25/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f7])).
% 3.25/0.99  
% 3.25/0.99  fof(f8,axiom,(
% 3.25/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f23,plain,(
% 3.25/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f8])).
% 3.25/0.99  
% 3.25/0.99  fof(f24,plain,(
% 3.25/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.25/0.99    inference(flattening,[],[f23])).
% 3.25/0.99  
% 3.25/0.99  fof(f54,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f24])).
% 3.25/0.99  
% 3.25/0.99  fof(f61,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f73,plain,(
% 3.25/0.99    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.25/0.99    inference(cnf_transformation,[],[f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f68,plain,(
% 3.25/0.99    v1_funct_1(sK4)),
% 3.25/0.99    inference(cnf_transformation,[],[f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f64,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f78,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f64])).
% 3.25/0.99  
% 3.25/0.99  fof(f79,plain,(
% 3.25/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f78])).
% 3.25/0.99  
% 3.25/0.99  fof(f4,axiom,(
% 3.25/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f34,plain,(
% 3.25/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/0.99    inference(nnf_transformation,[],[f4])).
% 3.25/0.99  
% 3.25/0.99  fof(f35,plain,(
% 3.25/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/0.99    inference(flattening,[],[f34])).
% 3.25/0.99  
% 3.25/0.99  fof(f49,plain,(
% 3.25/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.25/0.99    inference(cnf_transformation,[],[f35])).
% 3.25/0.99  
% 3.25/0.99  fof(f76,plain,(
% 3.25/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.25/0.99    inference(equality_resolution,[],[f49])).
% 3.25/0.99  
% 3.25/0.99  fof(f1,axiom,(
% 3.25/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f32,plain,(
% 3.25/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.25/0.99    inference(nnf_transformation,[],[f1])).
% 3.25/0.99  
% 3.25/0.99  fof(f33,plain,(
% 3.25/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.25/0.99    inference(flattening,[],[f32])).
% 3.25/0.99  
% 3.25/0.99  fof(f44,plain,(
% 3.25/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f33])).
% 3.25/1.00  
% 3.25/1.00  fof(f3,axiom,(
% 3.25/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f46,plain,(
% 3.25/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f3])).
% 3.25/1.00  
% 3.25/1.00  fof(f55,plain,(
% 3.25/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f36])).
% 3.25/1.00  
% 3.25/1.00  fof(f2,axiom,(
% 3.25/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f19,plain,(
% 3.25/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.25/1.00    inference(ennf_transformation,[],[f2])).
% 3.25/1.00  
% 3.25/1.00  fof(f20,plain,(
% 3.25/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.25/1.00    inference(flattening,[],[f19])).
% 3.25/1.00  
% 3.25/1.00  fof(f45,plain,(
% 3.25/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f20])).
% 3.25/1.00  
% 3.25/1.00  fof(f72,plain,(
% 3.25/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.25/1.00    inference(cnf_transformation,[],[f41])).
% 3.25/1.00  
% 3.25/1.00  fof(f60,plain,(
% 3.25/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f37])).
% 3.25/1.00  
% 3.25/1.00  fof(f82,plain,(
% 3.25/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.25/1.00    inference(equality_resolution,[],[f60])).
% 3.25/1.00  
% 3.25/1.00  fof(f48,plain,(
% 3.25/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.25/1.00    inference(cnf_transformation,[],[f35])).
% 3.25/1.00  
% 3.25/1.00  fof(f77,plain,(
% 3.25/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.25/1.00    inference(equality_resolution,[],[f48])).
% 3.25/1.00  
% 3.25/1.00  cnf(c_22,plain,
% 3.25/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.00      | k1_xboole_0 = X2 ),
% 3.25/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_30,negated_conjecture,
% 3.25/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.25/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_535,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.00      | sK2 != X2
% 3.25/1.00      | sK1 != X1
% 3.25/1.00      | sK4 != X0
% 3.25/1.00      | k1_xboole_0 = X2 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_536,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.25/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.25/1.00      | k1_xboole_0 = sK2 ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_29,negated_conjecture,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.25/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_538,plain,
% 3.25/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_536,c_29]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1311,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_16,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1314,plain,
% 3.25/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2792,plain,
% 3.25/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1311,c_1314]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3061,plain,
% 3.25/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_538,c_2792]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_28,negated_conjecture,
% 3.25/1.00      ( r1_tarski(sK2,sK3) ),
% 3.25/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1312,plain,
% 3.25/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_8,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1)
% 3.25/1.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 3.25/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1319,plain,
% 3.25/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.25/1.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_10,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 3.25/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1317,plain,
% 3.25/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.25/1.00      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_13,plain,
% 3.25/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1316,plain,
% 3.25/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.25/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_15,plain,
% 3.25/1.00      ( m1_subset_1(X0,X1)
% 3.25/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.25/1.00      | ~ r2_hidden(X0,X2) ),
% 3.25/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_11,plain,
% 3.25/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.25/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_12,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.25/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_370,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_371,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.25/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_385,plain,
% 3.25/1.00      ( m1_subset_1(X0,X1)
% 3.25/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 3.25/1.00      | X3 != X0
% 3.25/1.00      | k1_zfmisc_1(X4) != X2 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_371]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_386,plain,
% 3.25/1.00      ( m1_subset_1(X0,X1)
% 3.25/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.25/1.00      | ~ m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1)) ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1310,plain,
% 3.25/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.25/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.25/1.00      | m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1)) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2664,plain,
% 3.25/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.25/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.25/1.00      | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1316,c_1310]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_5314,plain,
% 3.25/1.00      ( m1_subset_1(sK4,X0) = iProver_top
% 3.25/1.00      | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)),X0) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1311,c_2664]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_5622,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
% 3.25/1.00      | r1_tarski(k2_zfmisc_1(sK1,sK2),X0) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1317,c_5314]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_5809,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.25/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1319,c_5622]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_6094,plain,
% 3.25/1.00      ( k1_relset_1(sK1,X0,sK4) = k1_relat_1(sK4)
% 3.25/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_5809,c_1314]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7196,plain,
% 3.25/1.00      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1312,c_6094]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_20,plain,
% 3.25/1.00      ( v1_funct_2(X0,X1,X2)
% 3.25/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.25/1.00      | k1_xboole_0 = X2 ),
% 3.25/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_26,negated_conjecture,
% 3.25/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.25/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | ~ v1_funct_1(sK4) ),
% 3.25/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_31,negated_conjecture,
% 3.25/1.00      ( v1_funct_1(sK4) ),
% 3.25/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_161,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_26,c_31]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_162,negated_conjecture,
% 3.25/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.25/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.25/1.00      inference(renaming,[status(thm)],[c_161]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_522,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.25/1.00      | sK3 != X2
% 3.25/1.00      | sK1 != X1
% 3.25/1.00      | sK4 != X0
% 3.25/1.00      | k1_xboole_0 = X2 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_162]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_523,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.25/1.00      | k1_xboole_0 = sK3 ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_522]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1305,plain,
% 3.25/1.00      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.25/1.00      | k1_xboole_0 = sK3
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7200,plain,
% 3.25/1.00      ( k1_relat_1(sK4) != sK1
% 3.25/1.00      | sK3 = k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7196,c_1305]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_35,plain,
% 3.25/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1506,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1507,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_17,plain,
% 3.25/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.25/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.25/1.00      | k1_xboole_0 = X0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_412,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.25/1.00      | sK3 != k1_xboole_0
% 3.25/1.00      | sK1 != X0
% 3.25/1.00      | sK4 != k1_xboole_0
% 3.25/1.00      | k1_xboole_0 = X0 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_162]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_413,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.25/1.00      | sK3 != k1_xboole_0
% 3.25/1.00      | sK4 != k1_xboole_0
% 3.25/1.00      | k1_xboole_0 = sK1 ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1309,plain,
% 3.25/1.00      ( sK3 != k1_xboole_0
% 3.25/1.00      | sK4 != k1_xboole_0
% 3.25/1.00      | k1_xboole_0 = sK1
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.25/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_5,plain,
% 3.25/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1443,plain,
% 3.25/1.00      ( sK3 != k1_xboole_0
% 3.25/1.00      | sK1 = k1_xboole_0
% 3.25/1.00      | sK4 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.25/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_1309,c_5]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_556,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | sK2 != sK3
% 3.25/1.00      | sK1 != sK1
% 3.25/1.00      | sK4 != sK4 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_162,c_30]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_557,plain,
% 3.25/1.00      ( sK2 != sK3
% 3.25/1.00      | sK1 != sK1
% 3.25/1.00      | sK4 != sK4
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_0,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.25/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1512,plain,
% 3.25/1.00      ( ~ r1_tarski(sK2,sK3) | ~ r1_tarski(sK3,sK2) | sK2 = sK3 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_810,plain,( X0 = X0 ),theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1585,plain,
% 3.25/1.00      ( sK1 = sK1 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1606,plain,
% 3.25/1.00      ( sK2 = sK2 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1794,plain,
% 3.25/1.00      ( sK4 = sK4 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_4,plain,
% 3.25/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1837,plain,
% 3.25/1.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_812,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.25/1.00      theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1595,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,sK2) | sK2 != X1 | sK3 != X0 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_812]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1855,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,sK2)
% 3.25/1.00      | r1_tarski(sK3,sK2)
% 3.25/1.00      | sK2 != sK2
% 3.25/1.00      | sK3 != X0 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1857,plain,
% 3.25/1.00      ( r1_tarski(sK3,sK2)
% 3.25/1.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.25/1.00      | sK2 != sK2
% 3.25/1.00      | sK3 != k1_xboole_0 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_1855]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1941,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.25/1.00      | sK3 != k1_xboole_0 ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_1443,c_28,c_557,c_1512,c_1585,c_1606,c_1794,c_1837,
% 3.25/1.00                 c_1857]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1942,plain,
% 3.25/1.00      ( sK3 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.25/1.00      inference(renaming,[status(thm)],[c_1941]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1943,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.25/1.00      | sK3 != k1_xboole_0 ),
% 3.25/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1942]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_14,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.25/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1315,plain,
% 3.25/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.25/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2151,plain,
% 3.25/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1311,c_1315]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2167,plain,
% 3.25/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
% 3.25/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2151]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.25/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1553,plain,
% 3.25/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK3))
% 3.25/1.00      | ~ r1_tarski(sK4,X0)
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1911,plain,
% 3.25/1.00      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK1,sK3))
% 3.25/1.00      | ~ r1_tarski(sK4,k2_zfmisc_1(X0,X1))
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3155,plain,
% 3.25/1.00      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
% 3.25/1.00      | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_1911]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3156,plain,
% 3.25/1.00      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) != iProver_top
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.25/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_3155]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3465,plain,
% 3.25/1.00      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
% 3.25/1.00      | ~ r1_tarski(sK2,sK3) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3466,plain,
% 3.25/1.00      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.25/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_3465]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7368,plain,
% 3.25/1.00      ( k1_relat_1(sK4) != sK1 ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_7200,c_28,c_35,c_1506,c_1507,c_1943,c_2151,c_2167,
% 3.25/1.00                 c_3155,c_3156,c_3465,c_3466]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7371,plain,
% 3.25/1.00      ( sK2 = k1_xboole_0 ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_3061,c_7368]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_27,negated_conjecture,
% 3.25/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.25/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7403,plain,
% 3.25/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7371,c_27]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7404,plain,
% 3.25/1.00      ( sK1 = k1_xboole_0 ),
% 3.25/1.00      inference(equality_resolution_simp,[status(thm)],[c_7403]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7612,plain,
% 3.25/1.00      ( k1_relat_1(sK4) != k1_xboole_0 ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7404,c_7368]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7395,plain,
% 3.25/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7371,c_2792]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_21,plain,
% 3.25/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.25/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_498,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.25/1.00      | sK2 != X1
% 3.25/1.00      | sK1 != k1_xboole_0
% 3.25/1.00      | sK4 != X0 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_499,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.25/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.25/1.00      | sK1 != k1_xboole_0 ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1306,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.25/1.00      | sK1 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_6,plain,
% 3.25/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1412,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.25/1.00      | sK1 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_1306,c_6]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7398,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.25/1.00      | sK1 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7371,c_1412]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7412,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.25/1.00      | k1_xboole_0 != k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_7398,c_7404]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7413,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.25/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.00      inference(equality_resolution_simp,[status(thm)],[c_7412]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7401,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7371,c_1311]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7408,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_7401,c_7404]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7410,plain,
% 3.25/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_7408,c_6]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7416,plain,
% 3.25/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 3.25/1.00      inference(forward_subsumption_resolution,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_7413,c_7410]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7423,plain,
% 3.25/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_7395,c_7404,c_7416]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(contradiction,plain,
% 3.25/1.00      ( $false ),
% 3.25/1.00      inference(minisat,[status(thm)],[c_7612,c_7423]) ).
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/1.00  
% 3.25/1.00  ------                               Statistics
% 3.25/1.00  
% 3.25/1.00  ------ General
% 3.25/1.00  
% 3.25/1.00  abstr_ref_over_cycles:                  0
% 3.25/1.00  abstr_ref_under_cycles:                 0
% 3.25/1.00  gc_basic_clause_elim:                   0
% 3.25/1.00  forced_gc_time:                         0
% 3.25/1.00  parsing_time:                           0.008
% 3.25/1.00  unif_index_cands_time:                  0.
% 3.25/1.00  unif_index_add_time:                    0.
% 3.25/1.00  orderings_time:                         0.
% 3.25/1.00  out_proof_time:                         0.01
% 3.25/1.00  total_time:                             0.2
% 3.25/1.00  num_of_symbols:                         47
% 3.25/1.00  num_of_terms:                           4700
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing
% 3.25/1.00  
% 3.25/1.00  num_of_splits:                          0
% 3.25/1.00  num_of_split_atoms:                     0
% 3.25/1.00  num_of_reused_defs:                     0
% 3.25/1.00  num_eq_ax_congr_red:                    9
% 3.25/1.00  num_of_sem_filtered_clauses:            3
% 3.25/1.00  num_of_subtypes:                        0
% 3.25/1.00  monotx_restored_types:                  0
% 3.25/1.00  sat_num_of_epr_types:                   0
% 3.25/1.00  sat_num_of_non_cyclic_types:            0
% 3.25/1.00  sat_guarded_non_collapsed_types:        0
% 3.25/1.00  num_pure_diseq_elim:                    0
% 3.25/1.00  simp_replaced_by:                       0
% 3.25/1.00  res_preprocessed:                       135
% 3.25/1.00  prep_upred:                             0
% 3.25/1.00  prep_unflattend:                        47
% 3.25/1.00  smt_new_axioms:                         0
% 3.25/1.00  pred_elim_cands:                        2
% 3.25/1.00  pred_elim:                              3
% 3.25/1.00  pred_elim_cl:                           0
% 3.25/1.00  pred_elim_cycles:                       5
% 3.25/1.00  merged_defs:                            8
% 3.25/1.00  merged_defs_ncl:                        0
% 3.25/1.00  bin_hyper_res:                          8
% 3.25/1.00  prep_cycles:                            4
% 3.25/1.00  pred_elim_time:                         0.006
% 3.25/1.00  splitting_time:                         0.
% 3.25/1.00  sem_filter_time:                        0.
% 3.25/1.00  monotx_time:                            0.
% 3.25/1.00  subtype_inf_time:                       0.
% 3.25/1.00  
% 3.25/1.00  ------ Problem properties
% 3.25/1.00  
% 3.25/1.00  clauses:                                29
% 3.25/1.00  conjectures:                            3
% 3.25/1.00  epr:                                    6
% 3.25/1.00  horn:                                   24
% 3.25/1.00  ground:                                 11
% 3.25/1.00  unary:                                  8
% 3.25/1.00  binary:                                 12
% 3.25/1.00  lits:                                   63
% 3.25/1.00  lits_eq:                                30
% 3.25/1.00  fd_pure:                                0
% 3.25/1.00  fd_pseudo:                              0
% 3.25/1.00  fd_cond:                                2
% 3.25/1.00  fd_pseudo_cond:                         1
% 3.25/1.00  ac_symbols:                             0
% 3.25/1.00  
% 3.25/1.00  ------ Propositional Solver
% 3.25/1.00  
% 3.25/1.00  prop_solver_calls:                      30
% 3.25/1.00  prop_fast_solver_calls:                 855
% 3.25/1.00  smt_solver_calls:                       0
% 3.25/1.00  smt_fast_solver_calls:                  0
% 3.25/1.00  prop_num_of_clauses:                    2632
% 3.25/1.00  prop_preprocess_simplified:             6590
% 3.25/1.00  prop_fo_subsumed:                       16
% 3.25/1.00  prop_solver_time:                       0.
% 3.25/1.00  smt_solver_time:                        0.
% 3.25/1.00  smt_fast_solver_time:                   0.
% 3.25/1.00  prop_fast_solver_time:                  0.
% 3.25/1.00  prop_unsat_core_time:                   0.
% 3.25/1.00  
% 3.25/1.00  ------ QBF
% 3.25/1.00  
% 3.25/1.00  qbf_q_res:                              0
% 3.25/1.00  qbf_num_tautologies:                    0
% 3.25/1.00  qbf_prep_cycles:                        0
% 3.25/1.00  
% 3.25/1.00  ------ BMC1
% 3.25/1.00  
% 3.25/1.00  bmc1_current_bound:                     -1
% 3.25/1.00  bmc1_last_solved_bound:                 -1
% 3.25/1.00  bmc1_unsat_core_size:                   -1
% 3.25/1.00  bmc1_unsat_core_parents_size:           -1
% 3.25/1.00  bmc1_merge_next_fun:                    0
% 3.25/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.25/1.00  
% 3.25/1.00  ------ Instantiation
% 3.25/1.00  
% 3.25/1.00  inst_num_of_clauses:                    816
% 3.25/1.00  inst_num_in_passive:                    278
% 3.25/1.00  inst_num_in_active:                     377
% 3.25/1.00  inst_num_in_unprocessed:                164
% 3.25/1.00  inst_num_of_loops:                      470
% 3.25/1.00  inst_num_of_learning_restarts:          0
% 3.25/1.00  inst_num_moves_active_passive:          89
% 3.25/1.00  inst_lit_activity:                      0
% 3.25/1.00  inst_lit_activity_moves:                0
% 3.25/1.00  inst_num_tautologies:                   0
% 3.25/1.00  inst_num_prop_implied:                  0
% 3.25/1.00  inst_num_existing_simplified:           0
% 3.25/1.00  inst_num_eq_res_simplified:             0
% 3.25/1.00  inst_num_child_elim:                    0
% 3.25/1.00  inst_num_of_dismatching_blockings:      291
% 3.25/1.00  inst_num_of_non_proper_insts:           1271
% 3.25/1.00  inst_num_of_duplicates:                 0
% 3.25/1.00  inst_inst_num_from_inst_to_res:         0
% 3.25/1.00  inst_dismatching_checking_time:         0.
% 3.25/1.00  
% 3.25/1.00  ------ Resolution
% 3.25/1.00  
% 3.25/1.00  res_num_of_clauses:                     0
% 3.25/1.00  res_num_in_passive:                     0
% 3.25/1.00  res_num_in_active:                      0
% 3.25/1.00  res_num_of_loops:                       139
% 3.25/1.00  res_forward_subset_subsumed:            45
% 3.25/1.00  res_backward_subset_subsumed:           6
% 3.25/1.00  res_forward_subsumed:                   0
% 3.25/1.00  res_backward_subsumed:                  0
% 3.25/1.00  res_forward_subsumption_resolution:     2
% 3.25/1.00  res_backward_subsumption_resolution:    0
% 3.25/1.00  res_clause_to_clause_subsumption:       725
% 3.25/1.00  res_orphan_elimination:                 0
% 3.25/1.00  res_tautology_del:                      151
% 3.25/1.00  res_num_eq_res_simplified:              1
% 3.25/1.00  res_num_sel_changes:                    0
% 3.25/1.00  res_moves_from_active_to_pass:          0
% 3.25/1.00  
% 3.25/1.00  ------ Superposition
% 3.25/1.00  
% 3.25/1.00  sup_time_total:                         0.
% 3.25/1.00  sup_time_generating:                    0.
% 3.25/1.00  sup_time_sim_full:                      0.
% 3.25/1.00  sup_time_sim_immed:                     0.
% 3.25/1.00  
% 3.25/1.00  sup_num_of_clauses:                     122
% 3.25/1.00  sup_num_in_active:                      47
% 3.25/1.00  sup_num_in_passive:                     75
% 3.25/1.00  sup_num_of_loops:                       92
% 3.25/1.00  sup_fw_superposition:                   183
% 3.25/1.00  sup_bw_superposition:                   46
% 3.25/1.00  sup_immediate_simplified:               69
% 3.25/1.00  sup_given_eliminated:                   0
% 3.25/1.00  comparisons_done:                       0
% 3.25/1.00  comparisons_avoided:                    4
% 3.25/1.00  
% 3.25/1.00  ------ Simplifications
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  sim_fw_subset_subsumed:                 10
% 3.25/1.00  sim_bw_subset_subsumed:                 8
% 3.25/1.00  sim_fw_subsumed:                        17
% 3.25/1.00  sim_bw_subsumed:                        0
% 3.25/1.00  sim_fw_subsumption_res:                 3
% 3.25/1.00  sim_bw_subsumption_res:                 0
% 3.25/1.00  sim_tautology_del:                      3
% 3.25/1.00  sim_eq_tautology_del:                   15
% 3.25/1.00  sim_eq_res_simp:                        4
% 3.25/1.00  sim_fw_demodulated:                     22
% 3.25/1.00  sim_bw_demodulated:                     45
% 3.25/1.00  sim_light_normalised:                   34
% 3.25/1.00  sim_joinable_taut:                      0
% 3.25/1.00  sim_joinable_simp:                      0
% 3.25/1.00  sim_ac_normalised:                      0
% 3.25/1.00  sim_smt_subsumption:                    0
% 3.25/1.00  
%------------------------------------------------------------------------------
