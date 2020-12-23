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
% DateTime   : Thu Dec  3 12:00:08 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 414 expanded)
%              Number of clauses        :   67 ( 143 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  394 (1892 expanded)
%              Number of equality atoms :  125 ( 375 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,
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

fof(f36,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35])).

fof(f59,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f34,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    & v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1557,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1918,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_wellord2(k1_xboole_0)))) ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_wellord2(k1_xboole_0))))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1917,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_wellord2(k1_xboole_0))))
    | ~ v1_xboole_0(k1_wellord2(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_349,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_350,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK1),X1)
    | ~ r1_tarski(k1_relat_1(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1724,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
    | ~ r1_tarski(k2_relat_1(sK1),X0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_1727,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1696,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1309,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_24])).

cnf(c_139,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_139])).

cnf(c_407,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_415,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_407,c_9])).

cnf(c_1308,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_1577,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1308])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1578,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1577])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1600,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1617,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1577,c_23,c_1578,c_1600])).

cnf(c_1311,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1623,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1617,c_1311])).

cnf(c_1640,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1623])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_139])).

cnf(c_487,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_372,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_373,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_631,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_373])).

cnf(c_686,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0 ),
    inference(bin_hyper_res,[status(thm)],[c_487,c_631])).

cnf(c_1299,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_1622,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1617,c_1299])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1622])).

cnf(c_761,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1608,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK1),X2)
    | X2 != X1
    | k1_relat_1(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1610,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1539,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | k2_relat_1(sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_276,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_277,plain,
    ( v1_funct_2(sK1,X0,X1)
    | ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_295,plain,
    ( v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X3)
    | X0 != X3
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_277])).

cnf(c_296,plain,
    ( v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_xboole_0(X2)
    | X4 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_296])).

cnf(c_503,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_505,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_352,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_80,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_74,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1922,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_wellord2(k1_xboole_0)))) ),
    inference(grounding,[status(thm)],[c_1918:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_1923,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_wellord2(k1_xboole_0))))
    | ~ v1_xboole_0(k1_wellord2(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_1917:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1922,c_1923,c_1727,c_1696,c_1640,c_1639,c_1610,c_1600,c_1539,c_505,c_373,c_352,c_80,c_74,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.76/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/1.00  
% 1.76/1.00  ------  iProver source info
% 1.76/1.00  
% 1.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/1.00  git: non_committed_changes: false
% 1.76/1.00  git: last_make_outside_of_git: false
% 1.76/1.00  
% 1.76/1.00  ------ 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options
% 1.76/1.00  
% 1.76/1.00  --out_options                           all
% 1.76/1.00  --tptp_safe_out                         true
% 1.76/1.00  --problem_path                          ""
% 1.76/1.00  --include_path                          ""
% 1.76/1.00  --clausifier                            res/vclausify_rel
% 1.76/1.00  --clausifier_options                    --mode clausify
% 1.76/1.00  --stdin                                 false
% 1.76/1.00  --stats_out                             all
% 1.76/1.00  
% 1.76/1.00  ------ General Options
% 1.76/1.00  
% 1.76/1.00  --fof                                   false
% 1.76/1.00  --time_out_real                         305.
% 1.76/1.00  --time_out_virtual                      -1.
% 1.76/1.00  --symbol_type_check                     false
% 1.76/1.00  --clausify_out                          false
% 1.76/1.00  --sig_cnt_out                           false
% 1.76/1.00  --trig_cnt_out                          false
% 1.76/1.00  --trig_cnt_out_tolerance                1.
% 1.76/1.00  --trig_cnt_out_sk_spl                   false
% 1.76/1.00  --abstr_cl_out                          false
% 1.76/1.00  
% 1.76/1.00  ------ Global Options
% 1.76/1.00  
% 1.76/1.00  --schedule                              default
% 1.76/1.00  --add_important_lit                     false
% 1.76/1.00  --prop_solver_per_cl                    1000
% 1.76/1.00  --min_unsat_core                        false
% 1.76/1.00  --soft_assumptions                      false
% 1.76/1.00  --soft_lemma_size                       3
% 1.76/1.00  --prop_impl_unit_size                   0
% 1.76/1.00  --prop_impl_unit                        []
% 1.76/1.00  --share_sel_clauses                     true
% 1.76/1.00  --reset_solvers                         false
% 1.76/1.00  --bc_imp_inh                            [conj_cone]
% 1.76/1.00  --conj_cone_tolerance                   3.
% 1.76/1.00  --extra_neg_conj                        none
% 1.76/1.00  --large_theory_mode                     true
% 1.76/1.00  --prolific_symb_bound                   200
% 1.76/1.00  --lt_threshold                          2000
% 1.76/1.00  --clause_weak_htbl                      true
% 1.76/1.00  --gc_record_bc_elim                     false
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing Options
% 1.76/1.00  
% 1.76/1.00  --preprocessing_flag                    true
% 1.76/1.00  --time_out_prep_mult                    0.1
% 1.76/1.00  --splitting_mode                        input
% 1.76/1.00  --splitting_grd                         true
% 1.76/1.00  --splitting_cvd                         false
% 1.76/1.00  --splitting_cvd_svl                     false
% 1.76/1.00  --splitting_nvd                         32
% 1.76/1.00  --sub_typing                            true
% 1.76/1.00  --prep_gs_sim                           true
% 1.76/1.00  --prep_unflatten                        true
% 1.76/1.00  --prep_res_sim                          true
% 1.76/1.00  --prep_upred                            true
% 1.76/1.00  --prep_sem_filter                       exhaustive
% 1.76/1.00  --prep_sem_filter_out                   false
% 1.76/1.00  --pred_elim                             true
% 1.76/1.00  --res_sim_input                         true
% 1.76/1.00  --eq_ax_congr_red                       true
% 1.76/1.00  --pure_diseq_elim                       true
% 1.76/1.00  --brand_transform                       false
% 1.76/1.00  --non_eq_to_eq                          false
% 1.76/1.00  --prep_def_merge                        true
% 1.76/1.00  --prep_def_merge_prop_impl              false
% 1.76/1.00  --prep_def_merge_mbd                    true
% 1.76/1.00  --prep_def_merge_tr_red                 false
% 1.76/1.00  --prep_def_merge_tr_cl                  false
% 1.76/1.00  --smt_preprocessing                     true
% 1.76/1.00  --smt_ac_axioms                         fast
% 1.76/1.00  --preprocessed_out                      false
% 1.76/1.00  --preprocessed_stats                    false
% 1.76/1.00  
% 1.76/1.00  ------ Abstraction refinement Options
% 1.76/1.00  
% 1.76/1.00  --abstr_ref                             []
% 1.76/1.00  --abstr_ref_prep                        false
% 1.76/1.00  --abstr_ref_until_sat                   false
% 1.76/1.00  --abstr_ref_sig_restrict                funpre
% 1.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/1.00  --abstr_ref_under                       []
% 1.76/1.00  
% 1.76/1.00  ------ SAT Options
% 1.76/1.00  
% 1.76/1.00  --sat_mode                              false
% 1.76/1.00  --sat_fm_restart_options                ""
% 1.76/1.00  --sat_gr_def                            false
% 1.76/1.00  --sat_epr_types                         true
% 1.76/1.00  --sat_non_cyclic_types                  false
% 1.76/1.00  --sat_finite_models                     false
% 1.76/1.00  --sat_fm_lemmas                         false
% 1.76/1.00  --sat_fm_prep                           false
% 1.76/1.00  --sat_fm_uc_incr                        true
% 1.76/1.00  --sat_out_model                         small
% 1.76/1.00  --sat_out_clauses                       false
% 1.76/1.00  
% 1.76/1.00  ------ QBF Options
% 1.76/1.00  
% 1.76/1.00  --qbf_mode                              false
% 1.76/1.00  --qbf_elim_univ                         false
% 1.76/1.00  --qbf_dom_inst                          none
% 1.76/1.00  --qbf_dom_pre_inst                      false
% 1.76/1.00  --qbf_sk_in                             false
% 1.76/1.00  --qbf_pred_elim                         true
% 1.76/1.00  --qbf_split                             512
% 1.76/1.00  
% 1.76/1.00  ------ BMC1 Options
% 1.76/1.00  
% 1.76/1.00  --bmc1_incremental                      false
% 1.76/1.00  --bmc1_axioms                           reachable_all
% 1.76/1.00  --bmc1_min_bound                        0
% 1.76/1.00  --bmc1_max_bound                        -1
% 1.76/1.00  --bmc1_max_bound_default                -1
% 1.76/1.00  --bmc1_symbol_reachability              true
% 1.76/1.00  --bmc1_property_lemmas                  false
% 1.76/1.00  --bmc1_k_induction                      false
% 1.76/1.00  --bmc1_non_equiv_states                 false
% 1.76/1.00  --bmc1_deadlock                         false
% 1.76/1.00  --bmc1_ucm                              false
% 1.76/1.00  --bmc1_add_unsat_core                   none
% 1.76/1.00  --bmc1_unsat_core_children              false
% 1.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/1.00  --bmc1_out_stat                         full
% 1.76/1.00  --bmc1_ground_init                      false
% 1.76/1.00  --bmc1_pre_inst_next_state              false
% 1.76/1.00  --bmc1_pre_inst_state                   false
% 1.76/1.00  --bmc1_pre_inst_reach_state             false
% 1.76/1.00  --bmc1_out_unsat_core                   false
% 1.76/1.00  --bmc1_aig_witness_out                  false
% 1.76/1.00  --bmc1_verbose                          false
% 1.76/1.00  --bmc1_dump_clauses_tptp                false
% 1.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.76/1.00  --bmc1_dump_file                        -
% 1.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.76/1.00  --bmc1_ucm_extend_mode                  1
% 1.76/1.00  --bmc1_ucm_init_mode                    2
% 1.76/1.00  --bmc1_ucm_cone_mode                    none
% 1.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.76/1.00  --bmc1_ucm_relax_model                  4
% 1.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/1.00  --bmc1_ucm_layered_model                none
% 1.76/1.00  --bmc1_ucm_max_lemma_size               10
% 1.76/1.00  
% 1.76/1.00  ------ AIG Options
% 1.76/1.00  
% 1.76/1.00  --aig_mode                              false
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation Options
% 1.76/1.00  
% 1.76/1.00  --instantiation_flag                    true
% 1.76/1.00  --inst_sos_flag                         false
% 1.76/1.00  --inst_sos_phase                        true
% 1.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel_side                     num_symb
% 1.76/1.00  --inst_solver_per_active                1400
% 1.76/1.00  --inst_solver_calls_frac                1.
% 1.76/1.00  --inst_passive_queue_type               priority_queues
% 1.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/1.00  --inst_passive_queues_freq              [25;2]
% 1.76/1.00  --inst_dismatching                      true
% 1.76/1.00  --inst_eager_unprocessed_to_passive     true
% 1.76/1.00  --inst_prop_sim_given                   true
% 1.76/1.00  --inst_prop_sim_new                     false
% 1.76/1.00  --inst_subs_new                         false
% 1.76/1.00  --inst_eq_res_simp                      false
% 1.76/1.00  --inst_subs_given                       false
% 1.76/1.00  --inst_orphan_elimination               true
% 1.76/1.00  --inst_learning_loop_flag               true
% 1.76/1.00  --inst_learning_start                   3000
% 1.76/1.00  --inst_learning_factor                  2
% 1.76/1.00  --inst_start_prop_sim_after_learn       3
% 1.76/1.00  --inst_sel_renew                        solver
% 1.76/1.00  --inst_lit_activity_flag                true
% 1.76/1.00  --inst_restr_to_given                   false
% 1.76/1.00  --inst_activity_threshold               500
% 1.76/1.00  --inst_out_proof                        true
% 1.76/1.00  
% 1.76/1.00  ------ Resolution Options
% 1.76/1.00  
% 1.76/1.00  --resolution_flag                       true
% 1.76/1.00  --res_lit_sel                           adaptive
% 1.76/1.00  --res_lit_sel_side                      none
% 1.76/1.00  --res_ordering                          kbo
% 1.76/1.00  --res_to_prop_solver                    active
% 1.76/1.00  --res_prop_simpl_new                    false
% 1.76/1.00  --res_prop_simpl_given                  true
% 1.76/1.00  --res_passive_queue_type                priority_queues
% 1.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/1.00  --res_passive_queues_freq               [15;5]
% 1.76/1.00  --res_forward_subs                      full
% 1.76/1.00  --res_backward_subs                     full
% 1.76/1.00  --res_forward_subs_resolution           true
% 1.76/1.00  --res_backward_subs_resolution          true
% 1.76/1.00  --res_orphan_elimination                true
% 1.76/1.00  --res_time_limit                        2.
% 1.76/1.00  --res_out_proof                         true
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Options
% 1.76/1.00  
% 1.76/1.00  --superposition_flag                    true
% 1.76/1.00  --sup_passive_queue_type                priority_queues
% 1.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.76/1.00  --demod_completeness_check              fast
% 1.76/1.00  --demod_use_ground                      true
% 1.76/1.00  --sup_to_prop_solver                    passive
% 1.76/1.00  --sup_prop_simpl_new                    true
% 1.76/1.00  --sup_prop_simpl_given                  true
% 1.76/1.00  --sup_fun_splitting                     false
% 1.76/1.00  --sup_smt_interval                      50000
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Simplification Setup
% 1.76/1.00  
% 1.76/1.00  --sup_indices_passive                   []
% 1.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_full_bw                           [BwDemod]
% 1.76/1.00  --sup_immed_triv                        [TrivRules]
% 1.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_immed_bw_main                     []
% 1.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  
% 1.76/1.00  ------ Combination Options
% 1.76/1.00  
% 1.76/1.00  --comb_res_mult                         3
% 1.76/1.00  --comb_sup_mult                         2
% 1.76/1.00  --comb_inst_mult                        10
% 1.76/1.00  
% 1.76/1.00  ------ Debug Options
% 1.76/1.00  
% 1.76/1.00  --dbg_backtrace                         false
% 1.76/1.00  --dbg_dump_prop_clauses                 false
% 1.76/1.00  --dbg_dump_prop_clauses_file            -
% 1.76/1.00  --dbg_out_stat                          false
% 1.76/1.00  ------ Parsing...
% 1.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/1.00  ------ Proving...
% 1.76/1.00  ------ Problem Properties 
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  clauses                                 25
% 1.76/1.00  conjectures                             1
% 1.76/1.00  EPR                                     5
% 1.76/1.00  Horn                                    22
% 1.76/1.00  unary                                   5
% 1.76/1.00  binary                                  8
% 1.76/1.00  lits                                    63
% 1.76/1.00  lits eq                                 21
% 1.76/1.00  fd_pure                                 0
% 1.76/1.00  fd_pseudo                               0
% 1.76/1.00  fd_cond                                 1
% 1.76/1.00  fd_pseudo_cond                          1
% 1.76/1.00  AC symbols                              0
% 1.76/1.00  
% 1.76/1.00  ------ Schedule dynamic 5 is on 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  ------ 
% 1.76/1.00  Current options:
% 1.76/1.00  ------ 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options
% 1.76/1.00  
% 1.76/1.00  --out_options                           all
% 1.76/1.00  --tptp_safe_out                         true
% 1.76/1.00  --problem_path                          ""
% 1.76/1.00  --include_path                          ""
% 1.76/1.00  --clausifier                            res/vclausify_rel
% 1.76/1.00  --clausifier_options                    --mode clausify
% 1.76/1.00  --stdin                                 false
% 1.76/1.00  --stats_out                             all
% 1.76/1.00  
% 1.76/1.00  ------ General Options
% 1.76/1.00  
% 1.76/1.00  --fof                                   false
% 1.76/1.00  --time_out_real                         305.
% 1.76/1.00  --time_out_virtual                      -1.
% 1.76/1.00  --symbol_type_check                     false
% 1.76/1.00  --clausify_out                          false
% 1.76/1.00  --sig_cnt_out                           false
% 1.76/1.00  --trig_cnt_out                          false
% 1.76/1.00  --trig_cnt_out_tolerance                1.
% 1.76/1.00  --trig_cnt_out_sk_spl                   false
% 1.76/1.00  --abstr_cl_out                          false
% 1.76/1.00  
% 1.76/1.00  ------ Global Options
% 1.76/1.00  
% 1.76/1.00  --schedule                              default
% 1.76/1.00  --add_important_lit                     false
% 1.76/1.00  --prop_solver_per_cl                    1000
% 1.76/1.00  --min_unsat_core                        false
% 1.76/1.00  --soft_assumptions                      false
% 1.76/1.00  --soft_lemma_size                       3
% 1.76/1.00  --prop_impl_unit_size                   0
% 1.76/1.00  --prop_impl_unit                        []
% 1.76/1.00  --share_sel_clauses                     true
% 1.76/1.00  --reset_solvers                         false
% 1.76/1.00  --bc_imp_inh                            [conj_cone]
% 1.76/1.00  --conj_cone_tolerance                   3.
% 1.76/1.00  --extra_neg_conj                        none
% 1.76/1.00  --large_theory_mode                     true
% 1.76/1.00  --prolific_symb_bound                   200
% 1.76/1.00  --lt_threshold                          2000
% 1.76/1.00  --clause_weak_htbl                      true
% 1.76/1.00  --gc_record_bc_elim                     false
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing Options
% 1.76/1.00  
% 1.76/1.00  --preprocessing_flag                    true
% 1.76/1.00  --time_out_prep_mult                    0.1
% 1.76/1.00  --splitting_mode                        input
% 1.76/1.00  --splitting_grd                         true
% 1.76/1.00  --splitting_cvd                         false
% 1.76/1.00  --splitting_cvd_svl                     false
% 1.76/1.00  --splitting_nvd                         32
% 1.76/1.00  --sub_typing                            true
% 1.76/1.00  --prep_gs_sim                           true
% 1.76/1.00  --prep_unflatten                        true
% 1.76/1.00  --prep_res_sim                          true
% 1.76/1.00  --prep_upred                            true
% 1.76/1.00  --prep_sem_filter                       exhaustive
% 1.76/1.00  --prep_sem_filter_out                   false
% 1.76/1.00  --pred_elim                             true
% 1.76/1.00  --res_sim_input                         true
% 1.76/1.00  --eq_ax_congr_red                       true
% 1.76/1.00  --pure_diseq_elim                       true
% 1.76/1.00  --brand_transform                       false
% 1.76/1.00  --non_eq_to_eq                          false
% 1.76/1.00  --prep_def_merge                        true
% 1.76/1.00  --prep_def_merge_prop_impl              false
% 1.76/1.00  --prep_def_merge_mbd                    true
% 1.76/1.00  --prep_def_merge_tr_red                 false
% 1.76/1.00  --prep_def_merge_tr_cl                  false
% 1.76/1.00  --smt_preprocessing                     true
% 1.76/1.00  --smt_ac_axioms                         fast
% 1.76/1.00  --preprocessed_out                      false
% 1.76/1.00  --preprocessed_stats                    false
% 1.76/1.00  
% 1.76/1.00  ------ Abstraction refinement Options
% 1.76/1.00  
% 1.76/1.00  --abstr_ref                             []
% 1.76/1.00  --abstr_ref_prep                        false
% 1.76/1.00  --abstr_ref_until_sat                   false
% 1.76/1.00  --abstr_ref_sig_restrict                funpre
% 1.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/1.00  --abstr_ref_under                       []
% 1.76/1.00  
% 1.76/1.00  ------ SAT Options
% 1.76/1.00  
% 1.76/1.00  --sat_mode                              false
% 1.76/1.00  --sat_fm_restart_options                ""
% 1.76/1.00  --sat_gr_def                            false
% 1.76/1.00  --sat_epr_types                         true
% 1.76/1.00  --sat_non_cyclic_types                  false
% 1.76/1.00  --sat_finite_models                     false
% 1.76/1.00  --sat_fm_lemmas                         false
% 1.76/1.00  --sat_fm_prep                           false
% 1.76/1.00  --sat_fm_uc_incr                        true
% 1.76/1.00  --sat_out_model                         small
% 1.76/1.00  --sat_out_clauses                       false
% 1.76/1.00  
% 1.76/1.00  ------ QBF Options
% 1.76/1.00  
% 1.76/1.00  --qbf_mode                              false
% 1.76/1.00  --qbf_elim_univ                         false
% 1.76/1.00  --qbf_dom_inst                          none
% 1.76/1.00  --qbf_dom_pre_inst                      false
% 1.76/1.00  --qbf_sk_in                             false
% 1.76/1.00  --qbf_pred_elim                         true
% 1.76/1.00  --qbf_split                             512
% 1.76/1.00  
% 1.76/1.00  ------ BMC1 Options
% 1.76/1.00  
% 1.76/1.00  --bmc1_incremental                      false
% 1.76/1.00  --bmc1_axioms                           reachable_all
% 1.76/1.00  --bmc1_min_bound                        0
% 1.76/1.00  --bmc1_max_bound                        -1
% 1.76/1.00  --bmc1_max_bound_default                -1
% 1.76/1.00  --bmc1_symbol_reachability              true
% 1.76/1.00  --bmc1_property_lemmas                  false
% 1.76/1.00  --bmc1_k_induction                      false
% 1.76/1.00  --bmc1_non_equiv_states                 false
% 1.76/1.00  --bmc1_deadlock                         false
% 1.76/1.00  --bmc1_ucm                              false
% 1.76/1.00  --bmc1_add_unsat_core                   none
% 1.76/1.00  --bmc1_unsat_core_children              false
% 1.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/1.00  --bmc1_out_stat                         full
% 1.76/1.00  --bmc1_ground_init                      false
% 1.76/1.00  --bmc1_pre_inst_next_state              false
% 1.76/1.00  --bmc1_pre_inst_state                   false
% 1.76/1.00  --bmc1_pre_inst_reach_state             false
% 1.76/1.00  --bmc1_out_unsat_core                   false
% 1.76/1.00  --bmc1_aig_witness_out                  false
% 1.76/1.00  --bmc1_verbose                          false
% 1.76/1.00  --bmc1_dump_clauses_tptp                false
% 1.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.76/1.00  --bmc1_dump_file                        -
% 1.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.76/1.00  --bmc1_ucm_extend_mode                  1
% 1.76/1.00  --bmc1_ucm_init_mode                    2
% 1.76/1.00  --bmc1_ucm_cone_mode                    none
% 1.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.76/1.00  --bmc1_ucm_relax_model                  4
% 1.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/1.00  --bmc1_ucm_layered_model                none
% 1.76/1.00  --bmc1_ucm_max_lemma_size               10
% 1.76/1.00  
% 1.76/1.00  ------ AIG Options
% 1.76/1.00  
% 1.76/1.00  --aig_mode                              false
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation Options
% 1.76/1.00  
% 1.76/1.00  --instantiation_flag                    true
% 1.76/1.00  --inst_sos_flag                         false
% 1.76/1.00  --inst_sos_phase                        true
% 1.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel_side                     none
% 1.76/1.00  --inst_solver_per_active                1400
% 1.76/1.00  --inst_solver_calls_frac                1.
% 1.76/1.00  --inst_passive_queue_type               priority_queues
% 1.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/1.00  --inst_passive_queues_freq              [25;2]
% 1.76/1.00  --inst_dismatching                      true
% 1.76/1.00  --inst_eager_unprocessed_to_passive     true
% 1.76/1.00  --inst_prop_sim_given                   true
% 1.76/1.00  --inst_prop_sim_new                     false
% 1.76/1.00  --inst_subs_new                         false
% 1.76/1.00  --inst_eq_res_simp                      false
% 1.76/1.00  --inst_subs_given                       false
% 1.76/1.00  --inst_orphan_elimination               true
% 1.76/1.00  --inst_learning_loop_flag               true
% 1.76/1.00  --inst_learning_start                   3000
% 1.76/1.00  --inst_learning_factor                  2
% 1.76/1.00  --inst_start_prop_sim_after_learn       3
% 1.76/1.00  --inst_sel_renew                        solver
% 1.76/1.00  --inst_lit_activity_flag                true
% 1.76/1.00  --inst_restr_to_given                   false
% 1.76/1.00  --inst_activity_threshold               500
% 1.76/1.00  --inst_out_proof                        true
% 1.76/1.00  
% 1.76/1.00  ------ Resolution Options
% 1.76/1.00  
% 1.76/1.00  --resolution_flag                       false
% 1.76/1.00  --res_lit_sel                           adaptive
% 1.76/1.00  --res_lit_sel_side                      none
% 1.76/1.00  --res_ordering                          kbo
% 1.76/1.00  --res_to_prop_solver                    active
% 1.76/1.00  --res_prop_simpl_new                    false
% 1.76/1.00  --res_prop_simpl_given                  true
% 1.76/1.00  --res_passive_queue_type                priority_queues
% 1.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/1.00  --res_passive_queues_freq               [15;5]
% 1.76/1.00  --res_forward_subs                      full
% 1.76/1.00  --res_backward_subs                     full
% 1.76/1.00  --res_forward_subs_resolution           true
% 1.76/1.00  --res_backward_subs_resolution          true
% 1.76/1.00  --res_orphan_elimination                true
% 1.76/1.00  --res_time_limit                        2.
% 1.76/1.00  --res_out_proof                         true
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Options
% 1.76/1.00  
% 1.76/1.00  --superposition_flag                    true
% 1.76/1.00  --sup_passive_queue_type                priority_queues
% 1.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.76/1.00  --demod_completeness_check              fast
% 1.76/1.00  --demod_use_ground                      true
% 1.76/1.00  --sup_to_prop_solver                    passive
% 1.76/1.00  --sup_prop_simpl_new                    true
% 1.76/1.00  --sup_prop_simpl_given                  true
% 1.76/1.00  --sup_fun_splitting                     false
% 1.76/1.00  --sup_smt_interval                      50000
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Simplification Setup
% 1.76/1.00  
% 1.76/1.00  --sup_indices_passive                   []
% 1.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_full_bw                           [BwDemod]
% 1.76/1.00  --sup_immed_triv                        [TrivRules]
% 1.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_immed_bw_main                     []
% 1.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  
% 1.76/1.00  ------ Combination Options
% 1.76/1.00  
% 1.76/1.00  --comb_res_mult                         3
% 1.76/1.00  --comb_sup_mult                         2
% 1.76/1.00  --comb_inst_mult                        10
% 1.76/1.00  
% 1.76/1.00  ------ Debug Options
% 1.76/1.00  
% 1.76/1.00  --dbg_backtrace                         false
% 1.76/1.00  --dbg_dump_prop_clauses                 false
% 1.76/1.00  --dbg_dump_prop_clauses_file            -
% 1.76/1.00  --dbg_out_stat                          false
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  ------ Proving...
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  % SZS status Theorem for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  fof(f4,axiom,(
% 1.76/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f42,plain,(
% 1.76/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f4])).
% 1.76/1.00  
% 1.76/1.00  fof(f7,axiom,(
% 1.76/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f20,plain,(
% 1.76/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.76/1.00    inference(ennf_transformation,[],[f7])).
% 1.76/1.00  
% 1.76/1.00  fof(f45,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f20])).
% 1.76/1.00  
% 1.76/1.00  fof(f9,axiom,(
% 1.76/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f22,plain,(
% 1.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.76/1.00    inference(ennf_transformation,[],[f9])).
% 1.76/1.00  
% 1.76/1.00  fof(f23,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.76/1.00    inference(flattening,[],[f22])).
% 1.76/1.00  
% 1.76/1.00  fof(f47,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f23])).
% 1.76/1.00  
% 1.76/1.00  fof(f14,conjecture,(
% 1.76/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f15,negated_conjecture,(
% 1.76/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.76/1.00    inference(negated_conjecture,[],[f14])).
% 1.76/1.00  
% 1.76/1.00  fof(f29,plain,(
% 1.76/1.00    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.76/1.00    inference(ennf_transformation,[],[f15])).
% 1.76/1.00  
% 1.76/1.00  fof(f30,plain,(
% 1.76/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.76/1.00    inference(flattening,[],[f29])).
% 1.76/1.00  
% 1.76/1.00  fof(f35,plain,(
% 1.76/1.00    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.76/1.00    introduced(choice_axiom,[])).
% 1.76/1.00  
% 1.76/1.00  fof(f36,plain,(
% 1.76/1.00    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35])).
% 1.76/1.00  
% 1.76/1.00  fof(f59,plain,(
% 1.76/1.00    v1_relat_1(sK1)),
% 1.76/1.00    inference(cnf_transformation,[],[f36])).
% 1.76/1.00  
% 1.76/1.00  fof(f3,axiom,(
% 1.76/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f41,plain,(
% 1.76/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f3])).
% 1.76/1.00  
% 1.76/1.00  fof(f13,axiom,(
% 1.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f27,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(ennf_transformation,[],[f13])).
% 1.76/1.00  
% 1.76/1.00  fof(f28,plain,(
% 1.76/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(flattening,[],[f27])).
% 1.76/1.00  
% 1.76/1.00  fof(f34,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(nnf_transformation,[],[f28])).
% 1.76/1.00  
% 1.76/1.00  fof(f55,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f34])).
% 1.76/1.00  
% 1.76/1.00  fof(f62,plain,(
% 1.76/1.00    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 1.76/1.00    inference(cnf_transformation,[],[f36])).
% 1.76/1.00  
% 1.76/1.00  fof(f60,plain,(
% 1.76/1.00    v1_funct_1(sK1)),
% 1.76/1.00    inference(cnf_transformation,[],[f36])).
% 1.76/1.00  
% 1.76/1.00  fof(f8,axiom,(
% 1.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f21,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(ennf_transformation,[],[f8])).
% 1.76/1.00  
% 1.76/1.00  fof(f46,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f21])).
% 1.76/1.00  
% 1.76/1.00  fof(f61,plain,(
% 1.76/1.00    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.76/1.00    inference(cnf_transformation,[],[f36])).
% 1.76/1.00  
% 1.76/1.00  fof(f1,axiom,(
% 1.76/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f31,plain,(
% 1.76/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/1.00    inference(nnf_transformation,[],[f1])).
% 1.76/1.00  
% 1.76/1.00  fof(f32,plain,(
% 1.76/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/1.00    inference(flattening,[],[f31])).
% 1.76/1.00  
% 1.76/1.00  fof(f37,plain,(
% 1.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.76/1.00    inference(cnf_transformation,[],[f32])).
% 1.76/1.00  
% 1.76/1.00  fof(f64,plain,(
% 1.76/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/1.00    inference(equality_resolution,[],[f37])).
% 1.76/1.00  
% 1.76/1.00  fof(f56,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f34])).
% 1.76/1.00  
% 1.76/1.00  fof(f68,plain,(
% 1.76/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.76/1.00    inference(equality_resolution,[],[f56])).
% 1.76/1.00  
% 1.76/1.00  fof(f6,axiom,(
% 1.76/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f19,plain,(
% 1.76/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.76/1.00    inference(ennf_transformation,[],[f6])).
% 1.76/1.00  
% 1.76/1.00  fof(f33,plain,(
% 1.76/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.76/1.00    inference(nnf_transformation,[],[f19])).
% 1.76/1.00  
% 1.76/1.00  fof(f44,plain,(
% 1.76/1.00    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f39,plain,(
% 1.76/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f32])).
% 1.76/1.00  
% 1.76/1.00  fof(f54,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f34])).
% 1.76/1.00  
% 1.76/1.00  fof(f69,plain,(
% 1.76/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.76/1.00    inference(equality_resolution,[],[f54])).
% 1.76/1.00  
% 1.76/1.00  fof(f12,axiom,(
% 1.76/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f26,plain,(
% 1.76/1.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.76/1.00    inference(ennf_transformation,[],[f12])).
% 1.76/1.00  
% 1.76/1.00  fof(f52,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f26])).
% 1.76/1.00  
% 1.76/1.00  fof(f11,axiom,(
% 1.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f24,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(ennf_transformation,[],[f11])).
% 1.76/1.00  
% 1.76/1.00  fof(f25,plain,(
% 1.76/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/1.00    inference(flattening,[],[f24])).
% 1.76/1.00  
% 1.76/1.00  fof(f51,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f25])).
% 1.76/1.00  
% 1.76/1.00  fof(f10,axiom,(
% 1.76/1.00    v1_xboole_0(k1_wellord2(k1_xboole_0)) & v1_relat_1(k1_wellord2(k1_xboole_0))),
% 1.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f49,plain,(
% 1.76/1.00    v1_xboole_0(k1_wellord2(k1_xboole_0))),
% 1.76/1.00    inference(cnf_transformation,[],[f10])).
% 1.76/1.00  
% 1.76/1.00  cnf(c_5,plain,
% 1.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1557,plain,
% 1.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1918,plain,
% 1.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_wellord2(k1_xboole_0)))) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_1557]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_8,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ v1_xboole_0(X2)
% 1.76/1.00      | v1_xboole_0(X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1545,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_wellord2(k1_xboole_0))))
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | ~ v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1917,plain,
% 1.76/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_wellord2(k1_xboole_0))))
% 1.76/1.00      | ~ v1_xboole_0(k1_wellord2(k1_xboole_0))
% 1.76/1.00      | v1_xboole_0(k1_xboole_0) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_1545]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_10,plain,
% 1.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.76/1.00      | ~ v1_relat_1(X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_25,negated_conjecture,
% 1.76/1.00      ( v1_relat_1(sK1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_349,plain,
% 1.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.76/1.00      | sK1 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_350,plain,
% 1.76/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(sK1),X1)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(sK1),X0) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1724,plain,
% 1.76/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X0)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(sK1),X0)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_350]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1727,plain,
% 1.76/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_1724]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_4,plain,
% 1.76/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1696,plain,
% 1.76/1.00      ( r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1309,plain,
% 1.76/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 1.76/1.00      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 1.76/1.00      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_19,plain,
% 1.76/1.00      ( v1_funct_2(X0,X1,X2)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | k1_relset_1(X1,X2,X0) != X1
% 1.76/1.00      | k1_xboole_0 = X2 ),
% 1.76/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_22,negated_conjecture,
% 1.76/1.00      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | ~ v1_funct_1(sK1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_24,negated_conjecture,
% 1.76/1.00      ( v1_funct_1(sK1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_138,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_22,c_24]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_139,negated_conjecture,
% 1.76/1.00      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 1.76/1.00      inference(renaming,[status(thm)],[c_138]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_406,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | k1_relset_1(X1,X2,X0) != X1
% 1.76/1.00      | k1_relat_1(sK1) != X1
% 1.76/1.00      | sK0 != X2
% 1.76/1.00      | sK1 != X0
% 1.76/1.00      | k1_xboole_0 = X2 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_139]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_407,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 1.76/1.00      | k1_xboole_0 = sK0 ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_9,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_415,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | k1_xboole_0 = sK0 ),
% 1.76/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_407,c_9]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1308,plain,
% 1.76/1.00      ( k1_xboole_0 = sK0
% 1.76/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1577,plain,
% 1.76/1.00      ( sK0 = k1_xboole_0
% 1.76/1.00      | r1_tarski(k2_relat_1(sK1),sK0) != iProver_top
% 1.76/1.00      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_1309,c_1308]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_23,negated_conjecture,
% 1.76/1.00      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1578,plain,
% 1.76/1.00      ( ~ r1_tarski(k2_relat_1(sK1),sK0)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 1.76/1.00      | sK0 = k1_xboole_0 ),
% 1.76/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1577]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2,plain,
% 1.76/1.00      ( r1_tarski(X0,X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1600,plain,
% 1.76/1.00      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1617,plain,
% 1.76/1.00      ( sK0 = k1_xboole_0 ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1577,c_23,c_1578,c_1600]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1311,plain,
% 1.76/1.00      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1623,plain,
% 1.76/1.00      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top ),
% 1.76/1.00      inference(demodulation,[status(thm)],[c_1617,c_1311]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1640,plain,
% 1.76/1.00      ( r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
% 1.76/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1623]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_18,plain,
% 1.76/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.76/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_486,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.76/1.00      | k1_relat_1(sK1) != k1_xboole_0
% 1.76/1.00      | sK0 != X1
% 1.76/1.00      | sK1 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_139]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_487,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.76/1.00      | k1_relat_1(sK1) != k1_xboole_0 ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_6,plain,
% 1.76/1.00      ( ~ v1_relat_1(X0)
% 1.76/1.00      | k2_relat_1(X0) != k1_xboole_0
% 1.76/1.00      | k1_relat_1(X0) = k1_xboole_0 ),
% 1.76/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_372,plain,
% 1.76/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 1.76/1.00      | k1_relat_1(X0) = k1_xboole_0
% 1.76/1.00      | sK1 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_373,plain,
% 1.76/1.00      ( k2_relat_1(sK1) != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_631,plain,
% 1.76/1.00      ( k2_relat_1(sK1) != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 1.76/1.00      inference(prop_impl,[status(thm)],[c_373]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_686,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.76/1.00      | k2_relat_1(sK1) != k1_xboole_0 ),
% 1.76/1.00      inference(bin_hyper_res,[status(thm)],[c_487,c_631]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1299,plain,
% 1.76/1.00      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 1.76/1.00      | k2_relat_1(sK1) != k1_xboole_0
% 1.76/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 1.76/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1622,plain,
% 1.76/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.76/1.00      | k2_relat_1(sK1) != k1_xboole_0
% 1.76/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
% 1.76/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.76/1.00      inference(demodulation,[status(thm)],[c_1617,c_1299]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1639,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.76/1.00      | k2_relat_1(sK1) != k1_xboole_0 ),
% 1.76/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1622]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_761,plain,
% 1.76/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.76/1.00      theory(equality) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1608,plain,
% 1.76/1.00      ( ~ r1_tarski(X0,X1)
% 1.76/1.00      | r1_tarski(k1_relat_1(sK1),X2)
% 1.76/1.00      | X2 != X1
% 1.76/1.00      | k1_relat_1(sK1) != X0 ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_761]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1610,plain,
% 1.76/1.00      ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
% 1.76/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.76/1.00      | k1_relat_1(sK1) != k1_xboole_0
% 1.76/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_1608]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_0,plain,
% 1.76/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.76/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1539,plain,
% 1.76/1.00      ( ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
% 1.76/1.00      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
% 1.76/1.00      | k2_relat_1(sK1) = k1_xboole_0 ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_20,plain,
% 1.76/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.76/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_15,plain,
% 1.76/1.00      ( v1_partfun1(X0,X1)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ v1_xboole_0(X1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_13,plain,
% 1.76/1.00      ( v1_funct_2(X0,X1,X2)
% 1.76/1.00      | ~ v1_partfun1(X0,X1)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | ~ v1_funct_1(X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_276,plain,
% 1.76/1.00      ( v1_funct_2(X0,X1,X2)
% 1.76/1.00      | ~ v1_partfun1(X0,X1)
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/1.00      | sK1 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_277,plain,
% 1.76/1.00      ( v1_funct_2(sK1,X0,X1)
% 1.76/1.00      | ~ v1_partfun1(sK1,X0)
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_276]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_295,plain,
% 1.76/1.00      ( v1_funct_2(sK1,X0,X1)
% 1.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.76/1.00      | ~ v1_xboole_0(X3)
% 1.76/1.00      | X0 != X3
% 1.76/1.00      | sK1 != X2 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_277]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_296,plain,
% 1.76/1.00      ( v1_funct_2(sK1,X0,X1)
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.76/1.00      | ~ v1_xboole_0(X0) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_502,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 1.76/1.00      | ~ v1_xboole_0(X2)
% 1.76/1.00      | X4 != X1
% 1.76/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.76/1.00      | sK1 != X0
% 1.76/1.00      | k1_xboole_0 != X2 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_296]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_503,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 1.76/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.76/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 1.76/1.00      | k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_502]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_505,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 1.76/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 1.76/1.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_503]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_352,plain,
% 1.76/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 1.76/1.00      | ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
% 1.76/1.00      | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_350]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_80,plain,
% 1.76/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.76/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_74,plain,
% 1.76/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_11,plain,
% 1.76/1.00      ( v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1922,plain,
% 1.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_wellord2(k1_xboole_0)))) ),
% 1.76/1.00      inference(grounding,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1918:[bind(X0,$fot(k1_xboole_0))]]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1923,plain,
% 1.76/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_wellord2(k1_xboole_0))))
% 1.76/1.00      | ~ v1_xboole_0(k1_wellord2(k1_xboole_0))
% 1.76/1.00      | v1_xboole_0(k1_xboole_0) ),
% 1.76/1.00      inference(grounding,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1917:[bind(X0,$fot(k1_xboole_0))]]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(contradiction,plain,
% 1.76/1.00      ( $false ),
% 1.76/1.00      inference(minisat,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1922,c_1923,c_1727,c_1696,c_1640,c_1639,c_1610,c_1600,
% 1.76/1.00                 c_1539,c_505,c_373,c_352,c_80,c_74,c_11]) ).
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  ------                               Statistics
% 1.76/1.00  
% 1.76/1.00  ------ General
% 1.76/1.00  
% 1.76/1.00  abstr_ref_over_cycles:                  0
% 1.76/1.00  abstr_ref_under_cycles:                 0
% 1.76/1.00  gc_basic_clause_elim:                   0
% 1.76/1.00  forced_gc_time:                         0
% 1.76/1.00  parsing_time:                           0.049
% 1.76/1.00  unif_index_cands_time:                  0.
% 1.76/1.00  unif_index_add_time:                    0.
% 1.76/1.00  orderings_time:                         0.
% 1.76/1.00  out_proof_time:                         0.017
% 1.76/1.00  total_time:                             0.131
% 1.76/1.00  num_of_symbols:                         50
% 1.76/1.00  num_of_terms:                           1213
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing
% 1.76/1.00  
% 1.76/1.00  num_of_splits:                          3
% 1.76/1.00  num_of_split_atoms:                     3
% 1.76/1.00  num_of_reused_defs:                     0
% 1.76/1.00  num_eq_ax_congr_red:                    4
% 1.76/1.00  num_of_sem_filtered_clauses:            1
% 1.76/1.00  num_of_subtypes:                        0
% 1.76/1.00  monotx_restored_types:                  0
% 1.76/1.00  sat_num_of_epr_types:                   0
% 1.76/1.00  sat_num_of_non_cyclic_types:            0
% 1.76/1.00  sat_guarded_non_collapsed_types:        0
% 1.76/1.00  num_pure_diseq_elim:                    0
% 1.76/1.00  simp_replaced_by:                       0
% 1.76/1.00  res_preprocessed:                       119
% 1.76/1.00  prep_upred:                             0
% 1.76/1.00  prep_unflattend:                        46
% 1.76/1.00  smt_new_axioms:                         0
% 1.76/1.00  pred_elim_cands:                        3
% 1.76/1.00  pred_elim:                              4
% 1.76/1.00  pred_elim_cl:                           2
% 1.76/1.00  pred_elim_cycles:                       6
% 1.76/1.00  merged_defs:                            12
% 1.76/1.00  merged_defs_ncl:                        0
% 1.76/1.00  bin_hyper_res:                          13
% 1.76/1.00  prep_cycles:                            4
% 1.76/1.00  pred_elim_time:                         0.006
% 1.76/1.00  splitting_time:                         0.
% 1.76/1.00  sem_filter_time:                        0.
% 1.76/1.00  monotx_time:                            0.
% 1.76/1.00  subtype_inf_time:                       0.
% 1.76/1.00  
% 1.76/1.00  ------ Problem properties
% 1.76/1.00  
% 1.76/1.00  clauses:                                25
% 1.76/1.00  conjectures:                            1
% 1.76/1.00  epr:                                    5
% 1.76/1.00  horn:                                   22
% 1.76/1.00  ground:                                 11
% 1.76/1.00  unary:                                  5
% 1.76/1.00  binary:                                 8
% 1.76/1.00  lits:                                   63
% 1.76/1.00  lits_eq:                                21
% 1.76/1.00  fd_pure:                                0
% 1.76/1.00  fd_pseudo:                              0
% 1.76/1.00  fd_cond:                                1
% 1.76/1.00  fd_pseudo_cond:                         1
% 1.76/1.00  ac_symbols:                             0
% 1.76/1.00  
% 1.76/1.00  ------ Propositional Solver
% 1.76/1.00  
% 1.76/1.00  prop_solver_calls:                      24
% 1.76/1.00  prop_fast_solver_calls:                 693
% 1.76/1.00  smt_solver_calls:                       0
% 1.76/1.00  smt_fast_solver_calls:                  0
% 1.76/1.00  prop_num_of_clauses:                    406
% 1.76/1.00  prop_preprocess_simplified:             3139
% 1.76/1.00  prop_fo_subsumed:                       6
% 1.76/1.00  prop_solver_time:                       0.
% 1.76/1.00  smt_solver_time:                        0.
% 1.76/1.00  smt_fast_solver_time:                   0.
% 1.76/1.00  prop_fast_solver_time:                  0.
% 1.76/1.00  prop_unsat_core_time:                   0.
% 1.76/1.00  
% 1.76/1.00  ------ QBF
% 1.76/1.00  
% 1.76/1.00  qbf_q_res:                              0
% 1.76/1.00  qbf_num_tautologies:                    0
% 1.76/1.00  qbf_prep_cycles:                        0
% 1.76/1.00  
% 1.76/1.00  ------ BMC1
% 1.76/1.00  
% 1.76/1.00  bmc1_current_bound:                     -1
% 1.76/1.00  bmc1_last_solved_bound:                 -1
% 1.76/1.00  bmc1_unsat_core_size:                   -1
% 1.76/1.00  bmc1_unsat_core_parents_size:           -1
% 1.76/1.00  bmc1_merge_next_fun:                    0
% 1.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation
% 1.76/1.00  
% 1.76/1.00  inst_num_of_clauses:                    127
% 1.76/1.00  inst_num_in_passive:                    5
% 1.76/1.00  inst_num_in_active:                     69
% 1.76/1.00  inst_num_in_unprocessed:                52
% 1.76/1.00  inst_num_of_loops:                      78
% 1.76/1.00  inst_num_of_learning_restarts:          0
% 1.76/1.00  inst_num_moves_active_passive:          7
% 1.76/1.00  inst_lit_activity:                      0
% 1.76/1.00  inst_lit_activity_moves:                0
% 1.76/1.00  inst_num_tautologies:                   0
% 1.76/1.00  inst_num_prop_implied:                  0
% 1.76/1.00  inst_num_existing_simplified:           0
% 1.76/1.00  inst_num_eq_res_simplified:             0
% 1.76/1.00  inst_num_child_elim:                    0
% 1.76/1.00  inst_num_of_dismatching_blockings:      8
% 1.76/1.00  inst_num_of_non_proper_insts:           86
% 1.76/1.00  inst_num_of_duplicates:                 0
% 1.76/1.00  inst_inst_num_from_inst_to_res:         0
% 1.76/1.00  inst_dismatching_checking_time:         0.
% 1.76/1.00  
% 1.76/1.00  ------ Resolution
% 1.76/1.00  
% 1.76/1.00  res_num_of_clauses:                     0
% 1.76/1.00  res_num_in_passive:                     0
% 1.76/1.00  res_num_in_active:                      0
% 1.76/1.00  res_num_of_loops:                       123
% 1.76/1.00  res_forward_subset_subsumed:            6
% 1.76/1.00  res_backward_subset_subsumed:           0
% 1.76/1.00  res_forward_subsumed:                   0
% 1.76/1.00  res_backward_subsumed:                  0
% 1.76/1.00  res_forward_subsumption_resolution:     2
% 1.76/1.00  res_backward_subsumption_resolution:    0
% 1.76/1.00  res_clause_to_clause_subsumption:       63
% 1.76/1.00  res_orphan_elimination:                 0
% 1.76/1.00  res_tautology_del:                      38
% 1.76/1.00  res_num_eq_res_simplified:              0
% 1.76/1.00  res_num_sel_changes:                    0
% 1.76/1.00  res_moves_from_active_to_pass:          0
% 1.76/1.00  
% 1.76/1.00  ------ Superposition
% 1.76/1.00  
% 1.76/1.00  sup_time_total:                         0.
% 1.76/1.00  sup_time_generating:                    0.
% 1.76/1.00  sup_time_sim_full:                      0.
% 1.76/1.00  sup_time_sim_immed:                     0.
% 1.76/1.00  
% 1.76/1.00  sup_num_of_clauses:                     27
% 1.76/1.00  sup_num_in_active:                      7
% 1.76/1.00  sup_num_in_passive:                     20
% 1.76/1.00  sup_num_of_loops:                       14
% 1.76/1.00  sup_fw_superposition:                   2
% 1.76/1.00  sup_bw_superposition:                   1
% 1.76/1.00  sup_immediate_simplified:               0
% 1.76/1.00  sup_given_eliminated:                   0
% 1.76/1.00  comparisons_done:                       0
% 1.76/1.00  comparisons_avoided:                    0
% 1.76/1.00  
% 1.76/1.00  ------ Simplifications
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  sim_fw_subset_subsumed:                 0
% 1.76/1.00  sim_bw_subset_subsumed:                 0
% 1.76/1.00  sim_fw_subsumed:                        1
% 1.76/1.00  sim_bw_subsumed:                        0
% 1.76/1.00  sim_fw_subsumption_res:                 1
% 1.76/1.00  sim_bw_subsumption_res:                 0
% 1.76/1.00  sim_tautology_del:                      0
% 1.76/1.00  sim_eq_tautology_del:                   1
% 1.76/1.00  sim_eq_res_simp:                        0
% 1.76/1.00  sim_fw_demodulated:                     0
% 1.76/1.00  sim_bw_demodulated:                     7
% 1.76/1.00  sim_light_normalised:                   0
% 1.76/1.00  sim_joinable_taut:                      0
% 1.76/1.00  sim_joinable_simp:                      0
% 1.76/1.00  sim_ac_normalised:                      0
% 1.76/1.00  sim_smt_subsumption:                    0
% 1.76/1.00  
%------------------------------------------------------------------------------
