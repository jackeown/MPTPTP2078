%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:47 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  194 (1695 expanded)
%              Number of clauses        :  107 ( 609 expanded)
%              Number of leaves         :   23 ( 308 expanded)
%              Depth                    :   23
%              Number of atoms          :  544 (5499 expanded)
%              Number of equality atoms :  186 (1170 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f66,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ~ r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f49,f66])).

fof(f105,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f38])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    ~ r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1591,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1569,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1574,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5237,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1574])).

cnf(c_34,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | r2_hidden(X0,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X4,X4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X4 != X2
    | X4 != X1
    | X3 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_32])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
    | r2_hidden(X2,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
    | r2_hidden(X2,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_556,c_35,c_33])).

cnf(c_1564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(X1,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_5503,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_1564])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_39,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6805,plain,
    ( r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5503,c_39])).

cnf(c_6806,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6805])).

cnf(c_6815,plain,
    ( r1_tarski(k5_partfun1(sK3,sK3,sK5),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r2_hidden(sK1(k5_partfun1(sK3,sK3,sK5),X0),k1_funct_2(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_6806])).

cnf(c_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1580,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_23,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_23])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_491,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_24])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_1567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_3102,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1580,c_1567])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1584,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3241,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3102,c_1584])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1578,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5495,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_1578])).

cnf(c_5905,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5495,c_1584])).

cnf(c_36,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_41,plain,
    ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_72,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_90,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2233,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2333,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2335,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_3104,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1567])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1586,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3706,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_1586])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_5901,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_5495])).

cnf(c_6344,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_5901])).

cnf(c_6354,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6344])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_34,c_31])).

cnf(c_512,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_35,c_33])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_512])).

cnf(c_1566,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_3365,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1566])).

cnf(c_4042,plain,
    ( r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_39])).

cnf(c_4043,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4042])).

cnf(c_4052,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK3,sK4,sK5),X0) = iProver_top
    | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),X0),k1_funct_2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_4043])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1592,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8781,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_1592])).

cnf(c_866,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9041,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_9043,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9041])).

cnf(c_9731,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5905,c_41,c_72,c_78,c_90,c_91,c_2233,c_2335,c_6354,c_8781,c_9043])).

cnf(c_9749,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK3,sK4,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9731,c_4043])).

cnf(c_10192,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9749,c_41,c_8781])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7619,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1573])).

cnf(c_1842,plain,
    ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4))
    | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1843,plain,
    ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) = iProver_top
    | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1842])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1939,plain,
    ( ~ r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5))
    | ~ v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1940,plain,
    ( r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) != iProver_top
    | v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1939])).

cnf(c_8264,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7619,c_39,c_41,c_1843,c_1940])).

cnf(c_10200,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10192,c_8264])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_101,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10508,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10200,c_101])).

cnf(c_1593,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2797,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1593])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1583,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2182,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1583])).

cnf(c_2899,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_2182])).

cnf(c_10513,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10508,c_2899])).

cnf(c_15188,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6815,c_3241,c_9731,c_10513])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1587,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15192,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15188,c_1587])).

cnf(c_15195,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15192,c_1592])).

cnf(c_1570,plain,
    ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9753,plain,
    ( r1_tarski(k5_partfun1(sK3,sK4,k1_xboole_0),k1_funct_2(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9731,c_1570])).

cnf(c_10199,plain,
    ( r1_tarski(k5_partfun1(sK3,k1_xboole_0,k1_xboole_0),k1_funct_2(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10192,c_9753])).

cnf(c_10744,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10513,c_10199])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15195,c_10744])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.31/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.04  
% 3.31/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.04  
% 3.31/1.04  ------  iProver source info
% 3.31/1.04  
% 3.31/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.04  git: non_committed_changes: false
% 3.31/1.04  git: last_make_outside_of_git: false
% 3.31/1.04  
% 3.31/1.04  ------ 
% 3.31/1.04  
% 3.31/1.04  ------ Input Options
% 3.31/1.04  
% 3.31/1.04  --out_options                           all
% 3.31/1.04  --tptp_safe_out                         true
% 3.31/1.04  --problem_path                          ""
% 3.31/1.04  --include_path                          ""
% 3.31/1.04  --clausifier                            res/vclausify_rel
% 3.31/1.04  --clausifier_options                    --mode clausify
% 3.31/1.04  --stdin                                 false
% 3.31/1.04  --stats_out                             all
% 3.31/1.04  
% 3.31/1.04  ------ General Options
% 3.31/1.04  
% 3.31/1.04  --fof                                   false
% 3.31/1.04  --time_out_real                         305.
% 3.31/1.04  --time_out_virtual                      -1.
% 3.31/1.04  --symbol_type_check                     false
% 3.31/1.04  --clausify_out                          false
% 3.31/1.04  --sig_cnt_out                           false
% 3.31/1.04  --trig_cnt_out                          false
% 3.31/1.04  --trig_cnt_out_tolerance                1.
% 3.31/1.04  --trig_cnt_out_sk_spl                   false
% 3.31/1.04  --abstr_cl_out                          false
% 3.31/1.04  
% 3.31/1.04  ------ Global Options
% 3.31/1.04  
% 3.31/1.04  --schedule                              default
% 3.31/1.04  --add_important_lit                     false
% 3.31/1.04  --prop_solver_per_cl                    1000
% 3.31/1.04  --min_unsat_core                        false
% 3.31/1.04  --soft_assumptions                      false
% 3.31/1.04  --soft_lemma_size                       3
% 3.31/1.04  --prop_impl_unit_size                   0
% 3.31/1.04  --prop_impl_unit                        []
% 3.31/1.04  --share_sel_clauses                     true
% 3.31/1.04  --reset_solvers                         false
% 3.31/1.04  --bc_imp_inh                            [conj_cone]
% 3.31/1.04  --conj_cone_tolerance                   3.
% 3.31/1.04  --extra_neg_conj                        none
% 3.31/1.04  --large_theory_mode                     true
% 3.31/1.04  --prolific_symb_bound                   200
% 3.31/1.04  --lt_threshold                          2000
% 3.31/1.04  --clause_weak_htbl                      true
% 3.31/1.04  --gc_record_bc_elim                     false
% 3.31/1.04  
% 3.31/1.04  ------ Preprocessing Options
% 3.31/1.04  
% 3.31/1.04  --preprocessing_flag                    true
% 3.31/1.04  --time_out_prep_mult                    0.1
% 3.31/1.04  --splitting_mode                        input
% 3.31/1.04  --splitting_grd                         true
% 3.31/1.04  --splitting_cvd                         false
% 3.31/1.04  --splitting_cvd_svl                     false
% 3.31/1.04  --splitting_nvd                         32
% 3.31/1.04  --sub_typing                            true
% 3.31/1.04  --prep_gs_sim                           true
% 3.31/1.04  --prep_unflatten                        true
% 3.31/1.04  --prep_res_sim                          true
% 3.31/1.04  --prep_upred                            true
% 3.31/1.04  --prep_sem_filter                       exhaustive
% 3.31/1.04  --prep_sem_filter_out                   false
% 3.31/1.04  --pred_elim                             true
% 3.31/1.04  --res_sim_input                         true
% 3.31/1.04  --eq_ax_congr_red                       true
% 3.31/1.04  --pure_diseq_elim                       true
% 3.31/1.04  --brand_transform                       false
% 3.31/1.04  --non_eq_to_eq                          false
% 3.31/1.04  --prep_def_merge                        true
% 3.31/1.04  --prep_def_merge_prop_impl              false
% 3.31/1.04  --prep_def_merge_mbd                    true
% 3.31/1.04  --prep_def_merge_tr_red                 false
% 3.31/1.04  --prep_def_merge_tr_cl                  false
% 3.31/1.04  --smt_preprocessing                     true
% 3.31/1.04  --smt_ac_axioms                         fast
% 3.31/1.04  --preprocessed_out                      false
% 3.31/1.04  --preprocessed_stats                    false
% 3.31/1.04  
% 3.31/1.04  ------ Abstraction refinement Options
% 3.31/1.04  
% 3.31/1.04  --abstr_ref                             []
% 3.31/1.04  --abstr_ref_prep                        false
% 3.31/1.04  --abstr_ref_until_sat                   false
% 3.31/1.04  --abstr_ref_sig_restrict                funpre
% 3.31/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.04  --abstr_ref_under                       []
% 3.31/1.04  
% 3.31/1.04  ------ SAT Options
% 3.31/1.04  
% 3.31/1.04  --sat_mode                              false
% 3.31/1.04  --sat_fm_restart_options                ""
% 3.31/1.04  --sat_gr_def                            false
% 3.31/1.04  --sat_epr_types                         true
% 3.31/1.04  --sat_non_cyclic_types                  false
% 3.31/1.04  --sat_finite_models                     false
% 3.31/1.04  --sat_fm_lemmas                         false
% 3.31/1.04  --sat_fm_prep                           false
% 3.31/1.05  --sat_fm_uc_incr                        true
% 3.31/1.05  --sat_out_model                         small
% 3.31/1.05  --sat_out_clauses                       false
% 3.31/1.05  
% 3.31/1.05  ------ QBF Options
% 3.31/1.05  
% 3.31/1.05  --qbf_mode                              false
% 3.31/1.05  --qbf_elim_univ                         false
% 3.31/1.05  --qbf_dom_inst                          none
% 3.31/1.05  --qbf_dom_pre_inst                      false
% 3.31/1.05  --qbf_sk_in                             false
% 3.31/1.05  --qbf_pred_elim                         true
% 3.31/1.05  --qbf_split                             512
% 3.31/1.05  
% 3.31/1.05  ------ BMC1 Options
% 3.31/1.05  
% 3.31/1.05  --bmc1_incremental                      false
% 3.31/1.05  --bmc1_axioms                           reachable_all
% 3.31/1.05  --bmc1_min_bound                        0
% 3.31/1.05  --bmc1_max_bound                        -1
% 3.31/1.05  --bmc1_max_bound_default                -1
% 3.31/1.05  --bmc1_symbol_reachability              true
% 3.31/1.05  --bmc1_property_lemmas                  false
% 3.31/1.05  --bmc1_k_induction                      false
% 3.31/1.05  --bmc1_non_equiv_states                 false
% 3.31/1.05  --bmc1_deadlock                         false
% 3.31/1.05  --bmc1_ucm                              false
% 3.31/1.05  --bmc1_add_unsat_core                   none
% 3.31/1.05  --bmc1_unsat_core_children              false
% 3.31/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.05  --bmc1_out_stat                         full
% 3.31/1.05  --bmc1_ground_init                      false
% 3.31/1.05  --bmc1_pre_inst_next_state              false
% 3.31/1.05  --bmc1_pre_inst_state                   false
% 3.31/1.05  --bmc1_pre_inst_reach_state             false
% 3.31/1.05  --bmc1_out_unsat_core                   false
% 3.31/1.05  --bmc1_aig_witness_out                  false
% 3.31/1.05  --bmc1_verbose                          false
% 3.31/1.05  --bmc1_dump_clauses_tptp                false
% 3.31/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.05  --bmc1_dump_file                        -
% 3.31/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.05  --bmc1_ucm_extend_mode                  1
% 3.31/1.05  --bmc1_ucm_init_mode                    2
% 3.31/1.05  --bmc1_ucm_cone_mode                    none
% 3.31/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.05  --bmc1_ucm_relax_model                  4
% 3.31/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.05  --bmc1_ucm_layered_model                none
% 3.31/1.05  --bmc1_ucm_max_lemma_size               10
% 3.31/1.05  
% 3.31/1.05  ------ AIG Options
% 3.31/1.05  
% 3.31/1.05  --aig_mode                              false
% 3.31/1.05  
% 3.31/1.05  ------ Instantiation Options
% 3.31/1.05  
% 3.31/1.05  --instantiation_flag                    true
% 3.31/1.05  --inst_sos_flag                         false
% 3.31/1.05  --inst_sos_phase                        true
% 3.31/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.05  --inst_lit_sel_side                     num_symb
% 3.31/1.05  --inst_solver_per_active                1400
% 3.31/1.05  --inst_solver_calls_frac                1.
% 3.31/1.05  --inst_passive_queue_type               priority_queues
% 3.31/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.05  --inst_passive_queues_freq              [25;2]
% 3.31/1.05  --inst_dismatching                      true
% 3.31/1.05  --inst_eager_unprocessed_to_passive     true
% 3.31/1.05  --inst_prop_sim_given                   true
% 3.31/1.05  --inst_prop_sim_new                     false
% 3.31/1.05  --inst_subs_new                         false
% 3.31/1.05  --inst_eq_res_simp                      false
% 3.31/1.05  --inst_subs_given                       false
% 3.31/1.05  --inst_orphan_elimination               true
% 3.31/1.05  --inst_learning_loop_flag               true
% 3.31/1.05  --inst_learning_start                   3000
% 3.31/1.05  --inst_learning_factor                  2
% 3.31/1.05  --inst_start_prop_sim_after_learn       3
% 3.31/1.05  --inst_sel_renew                        solver
% 3.31/1.05  --inst_lit_activity_flag                true
% 3.31/1.05  --inst_restr_to_given                   false
% 3.31/1.05  --inst_activity_threshold               500
% 3.31/1.05  --inst_out_proof                        true
% 3.31/1.05  
% 3.31/1.05  ------ Resolution Options
% 3.31/1.05  
% 3.31/1.05  --resolution_flag                       true
% 3.31/1.05  --res_lit_sel                           adaptive
% 3.31/1.05  --res_lit_sel_side                      none
% 3.31/1.05  --res_ordering                          kbo
% 3.31/1.05  --res_to_prop_solver                    active
% 3.31/1.05  --res_prop_simpl_new                    false
% 3.31/1.05  --res_prop_simpl_given                  true
% 3.31/1.05  --res_passive_queue_type                priority_queues
% 3.31/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.05  --res_passive_queues_freq               [15;5]
% 3.31/1.05  --res_forward_subs                      full
% 3.31/1.05  --res_backward_subs                     full
% 3.31/1.05  --res_forward_subs_resolution           true
% 3.31/1.05  --res_backward_subs_resolution          true
% 3.31/1.05  --res_orphan_elimination                true
% 3.31/1.05  --res_time_limit                        2.
% 3.31/1.05  --res_out_proof                         true
% 3.31/1.05  
% 3.31/1.05  ------ Superposition Options
% 3.31/1.05  
% 3.31/1.05  --superposition_flag                    true
% 3.31/1.05  --sup_passive_queue_type                priority_queues
% 3.31/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.05  --demod_completeness_check              fast
% 3.31/1.05  --demod_use_ground                      true
% 3.31/1.05  --sup_to_prop_solver                    passive
% 3.31/1.05  --sup_prop_simpl_new                    true
% 3.31/1.05  --sup_prop_simpl_given                  true
% 3.31/1.05  --sup_fun_splitting                     false
% 3.31/1.05  --sup_smt_interval                      50000
% 3.31/1.05  
% 3.31/1.05  ------ Superposition Simplification Setup
% 3.31/1.05  
% 3.31/1.05  --sup_indices_passive                   []
% 3.31/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_full_bw                           [BwDemod]
% 3.31/1.05  --sup_immed_triv                        [TrivRules]
% 3.31/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_immed_bw_main                     []
% 3.31/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.05  
% 3.31/1.05  ------ Combination Options
% 3.31/1.05  
% 3.31/1.05  --comb_res_mult                         3
% 3.31/1.05  --comb_sup_mult                         2
% 3.31/1.05  --comb_inst_mult                        10
% 3.31/1.05  
% 3.31/1.05  ------ Debug Options
% 3.31/1.05  
% 3.31/1.05  --dbg_backtrace                         false
% 3.31/1.05  --dbg_dump_prop_clauses                 false
% 3.31/1.05  --dbg_dump_prop_clauses_file            -
% 3.31/1.05  --dbg_out_stat                          false
% 3.31/1.05  ------ Parsing...
% 3.31/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.05  
% 3.31/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.31/1.05  
% 3.31/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.05  
% 3.31/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.05  ------ Proving...
% 3.31/1.05  ------ Problem Properties 
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  clauses                                 34
% 3.31/1.05  conjectures                             3
% 3.31/1.05  EPR                                     8
% 3.31/1.05  Horn                                    28
% 3.31/1.05  unary                                   9
% 3.31/1.05  binary                                  11
% 3.31/1.05  lits                                    81
% 3.31/1.05  lits eq                                 9
% 3.31/1.05  fd_pure                                 0
% 3.31/1.05  fd_pseudo                               0
% 3.31/1.05  fd_cond                                 4
% 3.31/1.05  fd_pseudo_cond                          1
% 3.31/1.05  AC symbols                              0
% 3.31/1.05  
% 3.31/1.05  ------ Schedule dynamic 5 is on 
% 3.31/1.05  
% 3.31/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  ------ 
% 3.31/1.05  Current options:
% 3.31/1.05  ------ 
% 3.31/1.05  
% 3.31/1.05  ------ Input Options
% 3.31/1.05  
% 3.31/1.05  --out_options                           all
% 3.31/1.05  --tptp_safe_out                         true
% 3.31/1.05  --problem_path                          ""
% 3.31/1.05  --include_path                          ""
% 3.31/1.05  --clausifier                            res/vclausify_rel
% 3.31/1.05  --clausifier_options                    --mode clausify
% 3.31/1.05  --stdin                                 false
% 3.31/1.05  --stats_out                             all
% 3.31/1.05  
% 3.31/1.05  ------ General Options
% 3.31/1.05  
% 3.31/1.05  --fof                                   false
% 3.31/1.05  --time_out_real                         305.
% 3.31/1.05  --time_out_virtual                      -1.
% 3.31/1.05  --symbol_type_check                     false
% 3.31/1.05  --clausify_out                          false
% 3.31/1.05  --sig_cnt_out                           false
% 3.31/1.05  --trig_cnt_out                          false
% 3.31/1.05  --trig_cnt_out_tolerance                1.
% 3.31/1.05  --trig_cnt_out_sk_spl                   false
% 3.31/1.05  --abstr_cl_out                          false
% 3.31/1.05  
% 3.31/1.05  ------ Global Options
% 3.31/1.05  
% 3.31/1.05  --schedule                              default
% 3.31/1.05  --add_important_lit                     false
% 3.31/1.05  --prop_solver_per_cl                    1000
% 3.31/1.05  --min_unsat_core                        false
% 3.31/1.05  --soft_assumptions                      false
% 3.31/1.05  --soft_lemma_size                       3
% 3.31/1.05  --prop_impl_unit_size                   0
% 3.31/1.05  --prop_impl_unit                        []
% 3.31/1.05  --share_sel_clauses                     true
% 3.31/1.05  --reset_solvers                         false
% 3.31/1.05  --bc_imp_inh                            [conj_cone]
% 3.31/1.05  --conj_cone_tolerance                   3.
% 3.31/1.05  --extra_neg_conj                        none
% 3.31/1.05  --large_theory_mode                     true
% 3.31/1.05  --prolific_symb_bound                   200
% 3.31/1.05  --lt_threshold                          2000
% 3.31/1.05  --clause_weak_htbl                      true
% 3.31/1.05  --gc_record_bc_elim                     false
% 3.31/1.05  
% 3.31/1.05  ------ Preprocessing Options
% 3.31/1.05  
% 3.31/1.05  --preprocessing_flag                    true
% 3.31/1.05  --time_out_prep_mult                    0.1
% 3.31/1.05  --splitting_mode                        input
% 3.31/1.05  --splitting_grd                         true
% 3.31/1.05  --splitting_cvd                         false
% 3.31/1.05  --splitting_cvd_svl                     false
% 3.31/1.05  --splitting_nvd                         32
% 3.31/1.05  --sub_typing                            true
% 3.31/1.05  --prep_gs_sim                           true
% 3.31/1.05  --prep_unflatten                        true
% 3.31/1.05  --prep_res_sim                          true
% 3.31/1.05  --prep_upred                            true
% 3.31/1.05  --prep_sem_filter                       exhaustive
% 3.31/1.05  --prep_sem_filter_out                   false
% 3.31/1.05  --pred_elim                             true
% 3.31/1.05  --res_sim_input                         true
% 3.31/1.05  --eq_ax_congr_red                       true
% 3.31/1.05  --pure_diseq_elim                       true
% 3.31/1.05  --brand_transform                       false
% 3.31/1.05  --non_eq_to_eq                          false
% 3.31/1.05  --prep_def_merge                        true
% 3.31/1.05  --prep_def_merge_prop_impl              false
% 3.31/1.05  --prep_def_merge_mbd                    true
% 3.31/1.05  --prep_def_merge_tr_red                 false
% 3.31/1.05  --prep_def_merge_tr_cl                  false
% 3.31/1.05  --smt_preprocessing                     true
% 3.31/1.05  --smt_ac_axioms                         fast
% 3.31/1.05  --preprocessed_out                      false
% 3.31/1.05  --preprocessed_stats                    false
% 3.31/1.05  
% 3.31/1.05  ------ Abstraction refinement Options
% 3.31/1.05  
% 3.31/1.05  --abstr_ref                             []
% 3.31/1.05  --abstr_ref_prep                        false
% 3.31/1.05  --abstr_ref_until_sat                   false
% 3.31/1.05  --abstr_ref_sig_restrict                funpre
% 3.31/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.05  --abstr_ref_under                       []
% 3.31/1.05  
% 3.31/1.05  ------ SAT Options
% 3.31/1.05  
% 3.31/1.05  --sat_mode                              false
% 3.31/1.05  --sat_fm_restart_options                ""
% 3.31/1.05  --sat_gr_def                            false
% 3.31/1.05  --sat_epr_types                         true
% 3.31/1.05  --sat_non_cyclic_types                  false
% 3.31/1.05  --sat_finite_models                     false
% 3.31/1.05  --sat_fm_lemmas                         false
% 3.31/1.05  --sat_fm_prep                           false
% 3.31/1.05  --sat_fm_uc_incr                        true
% 3.31/1.05  --sat_out_model                         small
% 3.31/1.05  --sat_out_clauses                       false
% 3.31/1.05  
% 3.31/1.05  ------ QBF Options
% 3.31/1.05  
% 3.31/1.05  --qbf_mode                              false
% 3.31/1.05  --qbf_elim_univ                         false
% 3.31/1.05  --qbf_dom_inst                          none
% 3.31/1.05  --qbf_dom_pre_inst                      false
% 3.31/1.05  --qbf_sk_in                             false
% 3.31/1.05  --qbf_pred_elim                         true
% 3.31/1.05  --qbf_split                             512
% 3.31/1.05  
% 3.31/1.05  ------ BMC1 Options
% 3.31/1.05  
% 3.31/1.05  --bmc1_incremental                      false
% 3.31/1.05  --bmc1_axioms                           reachable_all
% 3.31/1.05  --bmc1_min_bound                        0
% 3.31/1.05  --bmc1_max_bound                        -1
% 3.31/1.05  --bmc1_max_bound_default                -1
% 3.31/1.05  --bmc1_symbol_reachability              true
% 3.31/1.05  --bmc1_property_lemmas                  false
% 3.31/1.05  --bmc1_k_induction                      false
% 3.31/1.05  --bmc1_non_equiv_states                 false
% 3.31/1.05  --bmc1_deadlock                         false
% 3.31/1.05  --bmc1_ucm                              false
% 3.31/1.05  --bmc1_add_unsat_core                   none
% 3.31/1.05  --bmc1_unsat_core_children              false
% 3.31/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.05  --bmc1_out_stat                         full
% 3.31/1.05  --bmc1_ground_init                      false
% 3.31/1.05  --bmc1_pre_inst_next_state              false
% 3.31/1.05  --bmc1_pre_inst_state                   false
% 3.31/1.05  --bmc1_pre_inst_reach_state             false
% 3.31/1.05  --bmc1_out_unsat_core                   false
% 3.31/1.05  --bmc1_aig_witness_out                  false
% 3.31/1.05  --bmc1_verbose                          false
% 3.31/1.05  --bmc1_dump_clauses_tptp                false
% 3.31/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.05  --bmc1_dump_file                        -
% 3.31/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.05  --bmc1_ucm_extend_mode                  1
% 3.31/1.05  --bmc1_ucm_init_mode                    2
% 3.31/1.05  --bmc1_ucm_cone_mode                    none
% 3.31/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.05  --bmc1_ucm_relax_model                  4
% 3.31/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.05  --bmc1_ucm_layered_model                none
% 3.31/1.05  --bmc1_ucm_max_lemma_size               10
% 3.31/1.05  
% 3.31/1.05  ------ AIG Options
% 3.31/1.05  
% 3.31/1.05  --aig_mode                              false
% 3.31/1.05  
% 3.31/1.05  ------ Instantiation Options
% 3.31/1.05  
% 3.31/1.05  --instantiation_flag                    true
% 3.31/1.05  --inst_sos_flag                         false
% 3.31/1.05  --inst_sos_phase                        true
% 3.31/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.05  --inst_lit_sel_side                     none
% 3.31/1.05  --inst_solver_per_active                1400
% 3.31/1.05  --inst_solver_calls_frac                1.
% 3.31/1.05  --inst_passive_queue_type               priority_queues
% 3.31/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.05  --inst_passive_queues_freq              [25;2]
% 3.31/1.05  --inst_dismatching                      true
% 3.31/1.05  --inst_eager_unprocessed_to_passive     true
% 3.31/1.05  --inst_prop_sim_given                   true
% 3.31/1.05  --inst_prop_sim_new                     false
% 3.31/1.05  --inst_subs_new                         false
% 3.31/1.05  --inst_eq_res_simp                      false
% 3.31/1.05  --inst_subs_given                       false
% 3.31/1.05  --inst_orphan_elimination               true
% 3.31/1.05  --inst_learning_loop_flag               true
% 3.31/1.05  --inst_learning_start                   3000
% 3.31/1.05  --inst_learning_factor                  2
% 3.31/1.05  --inst_start_prop_sim_after_learn       3
% 3.31/1.05  --inst_sel_renew                        solver
% 3.31/1.05  --inst_lit_activity_flag                true
% 3.31/1.05  --inst_restr_to_given                   false
% 3.31/1.05  --inst_activity_threshold               500
% 3.31/1.05  --inst_out_proof                        true
% 3.31/1.05  
% 3.31/1.05  ------ Resolution Options
% 3.31/1.05  
% 3.31/1.05  --resolution_flag                       false
% 3.31/1.05  --res_lit_sel                           adaptive
% 3.31/1.05  --res_lit_sel_side                      none
% 3.31/1.05  --res_ordering                          kbo
% 3.31/1.05  --res_to_prop_solver                    active
% 3.31/1.05  --res_prop_simpl_new                    false
% 3.31/1.05  --res_prop_simpl_given                  true
% 3.31/1.05  --res_passive_queue_type                priority_queues
% 3.31/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.05  --res_passive_queues_freq               [15;5]
% 3.31/1.05  --res_forward_subs                      full
% 3.31/1.05  --res_backward_subs                     full
% 3.31/1.05  --res_forward_subs_resolution           true
% 3.31/1.05  --res_backward_subs_resolution          true
% 3.31/1.05  --res_orphan_elimination                true
% 3.31/1.05  --res_time_limit                        2.
% 3.31/1.05  --res_out_proof                         true
% 3.31/1.05  
% 3.31/1.05  ------ Superposition Options
% 3.31/1.05  
% 3.31/1.05  --superposition_flag                    true
% 3.31/1.05  --sup_passive_queue_type                priority_queues
% 3.31/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.05  --demod_completeness_check              fast
% 3.31/1.05  --demod_use_ground                      true
% 3.31/1.05  --sup_to_prop_solver                    passive
% 3.31/1.05  --sup_prop_simpl_new                    true
% 3.31/1.05  --sup_prop_simpl_given                  true
% 3.31/1.05  --sup_fun_splitting                     false
% 3.31/1.05  --sup_smt_interval                      50000
% 3.31/1.05  
% 3.31/1.05  ------ Superposition Simplification Setup
% 3.31/1.05  
% 3.31/1.05  --sup_indices_passive                   []
% 3.31/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_full_bw                           [BwDemod]
% 3.31/1.05  --sup_immed_triv                        [TrivRules]
% 3.31/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_immed_bw_main                     []
% 3.31/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.05  
% 3.31/1.05  ------ Combination Options
% 3.31/1.05  
% 3.31/1.05  --comb_res_mult                         3
% 3.31/1.05  --comb_sup_mult                         2
% 3.31/1.05  --comb_inst_mult                        10
% 3.31/1.05  
% 3.31/1.05  ------ Debug Options
% 3.31/1.05  
% 3.31/1.05  --dbg_backtrace                         false
% 3.31/1.05  --dbg_dump_prop_clauses                 false
% 3.31/1.05  --dbg_dump_prop_clauses_file            -
% 3.31/1.05  --dbg_out_stat                          false
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  ------ Proving...
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  % SZS status Theorem for theBenchmark.p
% 3.31/1.05  
% 3.31/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.05  
% 3.31/1.05  fof(f2,axiom,(
% 3.31/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f26,plain,(
% 3.31/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.31/1.05    inference(ennf_transformation,[],[f2])).
% 3.31/1.05  
% 3.31/1.05  fof(f54,plain,(
% 3.31/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.31/1.05    inference(nnf_transformation,[],[f26])).
% 3.31/1.05  
% 3.31/1.05  fof(f55,plain,(
% 3.31/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.31/1.05    inference(rectify,[],[f54])).
% 3.31/1.05  
% 3.31/1.05  fof(f56,plain,(
% 3.31/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.31/1.05    introduced(choice_axiom,[])).
% 3.31/1.05  
% 3.31/1.05  fof(f57,plain,(
% 3.31/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.31/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 3.31/1.05  
% 3.31/1.05  fof(f71,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f57])).
% 3.31/1.05  
% 3.31/1.05  fof(f23,conjecture,(
% 3.31/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f24,negated_conjecture,(
% 3.31/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.31/1.05    inference(negated_conjecture,[],[f23])).
% 3.31/1.05  
% 3.31/1.05  fof(f48,plain,(
% 3.31/1.05    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.31/1.05    inference(ennf_transformation,[],[f24])).
% 3.31/1.05  
% 3.31/1.05  fof(f49,plain,(
% 3.31/1.05    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.31/1.05    inference(flattening,[],[f48])).
% 3.31/1.05  
% 3.31/1.05  fof(f66,plain,(
% 3.31/1.05    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 3.31/1.05    introduced(choice_axiom,[])).
% 3.31/1.05  
% 3.31/1.05  fof(f67,plain,(
% 3.31/1.05    ~r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 3.31/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f49,f66])).
% 3.31/1.05  
% 3.31/1.05  fof(f105,plain,(
% 3.31/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.31/1.05    inference(cnf_transformation,[],[f67])).
% 3.31/1.05  
% 3.31/1.05  fof(f18,axiom,(
% 3.31/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f38,plain,(
% 3.31/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.31/1.05    inference(ennf_transformation,[],[f18])).
% 3.31/1.05  
% 3.31/1.05  fof(f39,plain,(
% 3.31/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.31/1.05    inference(flattening,[],[f38])).
% 3.31/1.05  
% 3.31/1.05  fof(f96,plain,(
% 3.31/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f39])).
% 3.31/1.05  
% 3.31/1.05  fof(f22,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f46,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.31/1.05    inference(ennf_transformation,[],[f22])).
% 3.31/1.05  
% 3.31/1.05  fof(f47,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.31/1.05    inference(flattening,[],[f46])).
% 3.31/1.05  
% 3.31/1.05  fof(f102,plain,(
% 3.31/1.05    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f47])).
% 3.31/1.05  
% 3.31/1.05  fof(f21,axiom,(
% 3.31/1.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f44,plain,(
% 3.31/1.05    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.31/1.05    inference(ennf_transformation,[],[f21])).
% 3.31/1.05  
% 3.31/1.05  fof(f45,plain,(
% 3.31/1.05    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.31/1.05    inference(flattening,[],[f44])).
% 3.31/1.05  
% 3.31/1.05  fof(f100,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f45])).
% 3.31/1.05  
% 3.31/1.05  fof(f101,plain,(
% 3.31/1.05    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f47])).
% 3.31/1.05  
% 3.31/1.05  fof(f103,plain,(
% 3.31/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f47])).
% 3.31/1.05  
% 3.31/1.05  fof(f104,plain,(
% 3.31/1.05    v1_funct_1(sK5)),
% 3.31/1.05    inference(cnf_transformation,[],[f67])).
% 3.31/1.05  
% 3.31/1.05  fof(f10,axiom,(
% 3.31/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f86,plain,(
% 3.31/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f10])).
% 3.31/1.05  
% 3.31/1.05  fof(f15,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f25,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.31/1.05    inference(pure_predicate_removal,[],[f15])).
% 3.31/1.05  
% 3.31/1.05  fof(f35,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.05    inference(ennf_transformation,[],[f25])).
% 3.31/1.05  
% 3.31/1.05  fof(f93,plain,(
% 3.31/1.05    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f35])).
% 3.31/1.05  
% 3.31/1.05  fof(f13,axiom,(
% 3.31/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f33,plain,(
% 3.31/1.05    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/1.05    inference(ennf_transformation,[],[f13])).
% 3.31/1.05  
% 3.31/1.05  fof(f65,plain,(
% 3.31/1.05    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.31/1.05    inference(nnf_transformation,[],[f33])).
% 3.31/1.05  
% 3.31/1.05  fof(f90,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f65])).
% 3.31/1.05  
% 3.31/1.05  fof(f14,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f34,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.05    inference(ennf_transformation,[],[f14])).
% 3.31/1.05  
% 3.31/1.05  fof(f92,plain,(
% 3.31/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f34])).
% 3.31/1.05  
% 3.31/1.05  fof(f8,axiom,(
% 3.31/1.05    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f29,plain,(
% 3.31/1.05    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 3.31/1.05    inference(ennf_transformation,[],[f8])).
% 3.31/1.05  
% 3.31/1.05  fof(f83,plain,(
% 3.31/1.05    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f29])).
% 3.31/1.05  
% 3.31/1.05  fof(f11,axiom,(
% 3.31/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f64,plain,(
% 3.31/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.31/1.05    inference(nnf_transformation,[],[f11])).
% 3.31/1.05  
% 3.31/1.05  fof(f87,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f64])).
% 3.31/1.05  
% 3.31/1.05  fof(f106,plain,(
% 3.31/1.05    ~r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4))),
% 3.31/1.05    inference(cnf_transformation,[],[f67])).
% 3.31/1.05  
% 3.31/1.05  fof(f7,axiom,(
% 3.31/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f60,plain,(
% 3.31/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.31/1.05    inference(nnf_transformation,[],[f7])).
% 3.31/1.05  
% 3.31/1.05  fof(f61,plain,(
% 3.31/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.31/1.05    inference(flattening,[],[f60])).
% 3.31/1.05  
% 3.31/1.05  fof(f79,plain,(
% 3.31/1.05    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f61])).
% 3.31/1.05  
% 3.31/1.05  fof(f80,plain,(
% 3.31/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.31/1.05    inference(cnf_transformation,[],[f61])).
% 3.31/1.05  
% 3.31/1.05  fof(f110,plain,(
% 3.31/1.05    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.31/1.05    inference(equality_resolution,[],[f80])).
% 3.31/1.05  
% 3.31/1.05  fof(f6,axiom,(
% 3.31/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f78,plain,(
% 3.31/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f6])).
% 3.31/1.05  
% 3.31/1.05  fof(f4,axiom,(
% 3.31/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f58,plain,(
% 3.31/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.05    inference(nnf_transformation,[],[f4])).
% 3.31/1.05  
% 3.31/1.05  fof(f59,plain,(
% 3.31/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.05    inference(flattening,[],[f58])).
% 3.31/1.05  
% 3.31/1.05  fof(f76,plain,(
% 3.31/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f59])).
% 3.31/1.05  
% 3.31/1.05  fof(f5,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f27,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.31/1.05    inference(ennf_transformation,[],[f5])).
% 3.31/1.05  
% 3.31/1.05  fof(f28,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.31/1.05    inference(flattening,[],[f27])).
% 3.31/1.05  
% 3.31/1.05  fof(f77,plain,(
% 3.31/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f28])).
% 3.31/1.05  
% 3.31/1.05  fof(f81,plain,(
% 3.31/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.31/1.05    inference(cnf_transformation,[],[f61])).
% 3.31/1.05  
% 3.31/1.05  fof(f109,plain,(
% 3.31/1.05    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.31/1.05    inference(equality_resolution,[],[f81])).
% 3.31/1.05  
% 3.31/1.05  fof(f20,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f42,plain,(
% 3.31/1.05    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.31/1.05    inference(ennf_transformation,[],[f20])).
% 3.31/1.05  
% 3.31/1.05  fof(f43,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.31/1.05    inference(flattening,[],[f42])).
% 3.31/1.05  
% 3.31/1.05  fof(f98,plain,(
% 3.31/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f43])).
% 3.31/1.05  
% 3.31/1.05  fof(f72,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f57])).
% 3.31/1.05  
% 3.31/1.05  fof(f19,axiom,(
% 3.31/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f40,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.31/1.05    inference(ennf_transformation,[],[f19])).
% 3.31/1.05  
% 3.31/1.05  fof(f41,plain,(
% 3.31/1.05    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.31/1.05    inference(flattening,[],[f40])).
% 3.31/1.05  
% 3.31/1.05  fof(f97,plain,(
% 3.31/1.05    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f41])).
% 3.31/1.05  
% 3.31/1.05  fof(f1,axiom,(
% 3.31/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f50,plain,(
% 3.31/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.31/1.05    inference(nnf_transformation,[],[f1])).
% 3.31/1.05  
% 3.31/1.05  fof(f51,plain,(
% 3.31/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.31/1.05    inference(rectify,[],[f50])).
% 3.31/1.05  
% 3.31/1.05  fof(f52,plain,(
% 3.31/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.31/1.05    introduced(choice_axiom,[])).
% 3.31/1.05  
% 3.31/1.05  fof(f53,plain,(
% 3.31/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.31/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 3.31/1.05  
% 3.31/1.05  fof(f68,plain,(
% 3.31/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.31/1.05    inference(cnf_transformation,[],[f53])).
% 3.31/1.05  
% 3.31/1.05  fof(f3,axiom,(
% 3.31/1.05    v1_xboole_0(k1_xboole_0)),
% 3.31/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.05  
% 3.31/1.05  fof(f73,plain,(
% 3.31/1.05    v1_xboole_0(k1_xboole_0)),
% 3.31/1.05    inference(cnf_transformation,[],[f3])).
% 3.31/1.05  
% 3.31/1.05  fof(f82,plain,(
% 3.31/1.05    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 3.31/1.05    inference(cnf_transformation,[],[f29])).
% 3.31/1.05  
% 3.31/1.05  fof(f74,plain,(
% 3.31/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.31/1.05    inference(cnf_transformation,[],[f59])).
% 3.31/1.05  
% 3.31/1.05  fof(f108,plain,(
% 3.31/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.31/1.05    inference(equality_resolution,[],[f74])).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1591,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) = iProver_top
% 3.31/1.05      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_37,negated_conjecture,
% 3.31/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.31/1.05      inference(cnf_transformation,[],[f105]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1569,plain,
% 3.31/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_28,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.31/1.05      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.31/1.05      inference(cnf_transformation,[],[f96]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1574,plain,
% 3.31/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.31/1.05      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5237,plain,
% 3.31/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.31/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1569,c_1574]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_34,plain,
% 3.31/1.05      ( v1_funct_2(X0,X1,X2)
% 3.31/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 3.31/1.05      | ~ v1_funct_1(X3) ),
% 3.31/1.05      inference(cnf_transformation,[],[f102]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_32,plain,
% 3.31/1.05      ( ~ v1_funct_2(X0,X1,X1)
% 3.31/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(X1,X1))
% 3.31/1.05      | ~ v1_funct_1(X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f100]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_555,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
% 3.31/1.05      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | r2_hidden(X3,k1_funct_2(X4,X4))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | ~ v1_funct_1(X3)
% 3.31/1.05      | X4 != X2
% 3.31/1.05      | X4 != X1
% 3.31/1.05      | X3 != X5 ),
% 3.31/1.05      inference(resolution_lifted,[status(thm)],[c_34,c_32]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_556,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.31/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.31/1.05      | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
% 3.31/1.05      | r2_hidden(X2,k1_funct_2(X1,X1))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | ~ v1_funct_1(X2) ),
% 3.31/1.05      inference(unflattening,[status(thm)],[c_555]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_35,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | v1_funct_1(X3) ),
% 3.31/1.05      inference(cnf_transformation,[],[f101]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_33,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | ~ v1_funct_1(X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f103]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_570,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.31/1.05      | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
% 3.31/1.05      | r2_hidden(X2,k1_funct_2(X1,X1))
% 3.31/1.05      | ~ v1_funct_1(X0) ),
% 3.31/1.05      inference(forward_subsumption_resolution,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_556,c_35,c_33]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1564,plain,
% 3.31/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.31/1.05      | r2_hidden(X2,k5_partfun1(X1,X1,X0)) != iProver_top
% 3.31/1.05      | r2_hidden(X2,k1_funct_2(X1,X1)) = iProver_top
% 3.31/1.05      | v1_funct_1(X0) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5503,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top
% 3.31/1.05      | v1_funct_1(sK5) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_5237,c_1564]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_38,negated_conjecture,
% 3.31/1.05      ( v1_funct_1(sK5) ),
% 3.31/1.05      inference(cnf_transformation,[],[f104]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_39,plain,
% 3.31/1.05      ( v1_funct_1(sK5) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6805,plain,
% 3.31/1.05      ( r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
% 3.31/1.05      | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_5503,c_39]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6806,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK3,sK5)) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(sK3,sK3)) = iProver_top ),
% 3.31/1.05      inference(renaming,[status(thm)],[c_6805]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6815,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK3,sK5),X0) = iProver_top
% 3.31/1.05      | r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(sK3,sK3,sK5),X0),k1_funct_2(sK3,sK3)) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1591,c_6806]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_18,plain,
% 3.31/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.31/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1580,plain,
% 3.31/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_25,plain,
% 3.31/1.05      ( v5_relat_1(X0,X1)
% 3.31/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.31/1.05      inference(cnf_transformation,[],[f93]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_23,plain,
% 3.31/1.05      ( ~ v5_relat_1(X0,X1)
% 3.31/1.05      | r1_tarski(k2_relat_1(X0),X1)
% 3.31/1.05      | ~ v1_relat_1(X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f90]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_487,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | r1_tarski(k2_relat_1(X0),X2)
% 3.31/1.05      | ~ v1_relat_1(X0) ),
% 3.31/1.05      inference(resolution,[status(thm)],[c_25,c_23]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_24,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | v1_relat_1(X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f92]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_491,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(X0),X2)
% 3.31/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_487,c_24]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_492,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.31/1.05      inference(renaming,[status(thm)],[c_491]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1567,plain,
% 3.31/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.05      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3102,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1580,c_1567]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_14,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1584,plain,
% 3.31/1.05      ( k1_xboole_0 = X0
% 3.31/1.05      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3241,plain,
% 3.31/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_3102,c_1584]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_20,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.31/1.05      inference(cnf_transformation,[],[f87]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1578,plain,
% 3.31/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.31/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5495,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.31/1.05      | r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_5237,c_1578]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5905,plain,
% 3.31/1.05      ( sK5 = k1_xboole_0
% 3.31/1.05      | r1_tarski(k2_relat_1(sK5),sK5) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_5495,c_1584]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_36,negated_conjecture,
% 3.31/1.05      ( ~ r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) ),
% 3.31/1.05      inference(cnf_transformation,[],[f106]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_41,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_72,plain,
% 3.31/1.05      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.31/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_78,plain,
% 3.31/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_13,plain,
% 3.31/1.05      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.31/1.05      | k1_xboole_0 = X1
% 3.31/1.05      | k1_xboole_0 = X0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_90,plain,
% 3.31/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.31/1.05      | k1_xboole_0 = k1_xboole_0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_12,plain,
% 3.31/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f110]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_91,plain,
% 3.31/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_12]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10,plain,
% 3.31/1.05      ( r1_tarski(k1_xboole_0,X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2233,plain,
% 3.31/1.05      ( r1_tarski(k1_xboole_0,sK5) ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2333,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2335,plain,
% 3.31/1.05      ( ~ r1_tarski(sK5,k1_xboole_0)
% 3.31/1.05      | ~ r1_tarski(k1_xboole_0,sK5)
% 3.31/1.05      | sK5 = k1_xboole_0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_2333]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3104,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1569,c_1567]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.31/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1586,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) != iProver_top
% 3.31/1.05      | r1_tarski(X1,X2) != iProver_top
% 3.31/1.05      | r1_tarski(X0,X2) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3706,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 3.31/1.05      | r1_tarski(sK4,X0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_3104,c_1586]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_11,plain,
% 3.31/1.05      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f109]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5901,plain,
% 3.31/1.05      ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.31/1.05      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_11,c_5495]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6344,plain,
% 3.31/1.05      ( r1_tarski(sK5,k1_xboole_0) = iProver_top
% 3.31/1.05      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_3706,c_5901]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_6354,plain,
% 3.31/1.05      ( r1_tarski(sK5,k1_xboole_0) | ~ r1_tarski(sK4,k1_xboole_0) ),
% 3.31/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_6344]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_31,plain,
% 3.31/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.31/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | k1_xboole_0 = X2 ),
% 3.31/1.05      inference(cnf_transformation,[],[f98]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_508,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | ~ v1_funct_1(X3)
% 3.31/1.05      | k1_xboole_0 = X2 ),
% 3.31/1.05      inference(resolution,[status(thm)],[c_34,c_31]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_512,plain,
% 3.31/1.05      ( ~ v1_funct_1(X0)
% 3.31/1.05      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.31/1.05      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | k1_xboole_0 = X2 ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_508,c_35,c_33]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_513,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.31/1.05      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | k1_xboole_0 = X2 ),
% 3.31/1.05      inference(renaming,[status(thm)],[c_512]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1566,plain,
% 3.31/1.05      ( k1_xboole_0 = X0
% 3.31/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.31/1.05      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 3.31/1.05      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 3.31/1.05      | v1_funct_1(X1) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_3365,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top
% 3.31/1.05      | v1_funct_1(sK5) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1569,c_1566]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_4042,plain,
% 3.31/1.05      ( r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
% 3.31/1.05      | sK4 = k1_xboole_0 ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_3365,c_39]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_4043,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK4,sK5)) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top ),
% 3.31/1.05      inference(renaming,[status(thm)],[c_4042]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_4052,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0
% 3.31/1.05      | r1_tarski(k5_partfun1(sK3,sK4,sK5),X0) = iProver_top
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),X0),k1_funct_2(sK3,sK4)) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1591,c_4043]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.31/1.05      inference(cnf_transformation,[],[f72]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1592,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) = iProver_top
% 3.31/1.05      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_8781,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0
% 3.31/1.05      | r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_4052,c_1592]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_866,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/1.05      theory(equality) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9041,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_866]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9043,plain,
% 3.31/1.05      ( r1_tarski(sK4,k1_xboole_0)
% 3.31/1.05      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.31/1.05      | sK4 != k1_xboole_0
% 3.31/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_9041]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9731,plain,
% 3.31/1.05      ( sK5 = k1_xboole_0 ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_5905,c_41,c_72,c_78,c_90,c_91,c_2233,c_2335,c_6354,
% 3.31/1.05                 c_8781,c_9043]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9749,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0
% 3.31/1.05      | r2_hidden(X0,k5_partfun1(sK3,sK4,k1_xboole_0)) != iProver_top
% 3.31/1.05      | r2_hidden(X0,k1_funct_2(sK3,sK4)) = iProver_top ),
% 3.31/1.05      inference(demodulation,[status(thm)],[c_9731,c_4043]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10192,plain,
% 3.31/1.05      ( sK4 = k1_xboole_0 ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_9749,c_41,c_8781]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_29,plain,
% 3.31/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.05      | ~ v1_funct_1(X0)
% 3.31/1.05      | ~ v1_xboole_0(X2)
% 3.31/1.05      | v1_xboole_0(X1)
% 3.31/1.05      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 3.31/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1573,plain,
% 3.31/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.05      | v1_funct_1(X0) != iProver_top
% 3.31/1.05      | v1_xboole_0(X2) != iProver_top
% 3.31/1.05      | v1_xboole_0(X1) = iProver_top
% 3.31/1.05      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_7619,plain,
% 3.31/1.05      ( v1_funct_1(sK5) != iProver_top
% 3.31/1.05      | v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) = iProver_top
% 3.31/1.05      | v1_xboole_0(sK4) != iProver_top
% 3.31/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1569,c_1573]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1842,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4))
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1843,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) = iProver_top
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_1842]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1,plain,
% 3.31/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.31/1.05      inference(cnf_transformation,[],[f68]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1939,plain,
% 3.31/1.05      ( ~ r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5))
% 3.31/1.05      | ~ v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) ),
% 3.31/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1940,plain,
% 3.31/1.05      ( r2_hidden(sK1(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)),k5_partfun1(sK3,sK4,sK5)) != iProver_top
% 3.31/1.05      | v1_xboole_0(k5_partfun1(sK3,sK4,sK5)) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_1939]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_8264,plain,
% 3.31/1.05      ( v1_xboole_0(sK4) != iProver_top
% 3.31/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_7619,c_39,c_41,c_1843,c_1940]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10200,plain,
% 3.31/1.05      ( v1_xboole_0(sK3) = iProver_top
% 3.31/1.05      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.31/1.05      inference(demodulation,[status(thm)],[c_10192,c_8264]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_5,plain,
% 3.31/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f73]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_101,plain,
% 3.31/1.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10508,plain,
% 3.31/1.05      ( v1_xboole_0(sK3) = iProver_top ),
% 3.31/1.05      inference(global_propositional_subsumption,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_10200,c_101]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1593,plain,
% 3.31/1.05      ( r2_hidden(X0,X1) != iProver_top
% 3.31/1.05      | v1_xboole_0(X1) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2797,plain,
% 3.31/1.05      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_1591,c_1593]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_15,plain,
% 3.31/1.05      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 3.31/1.05      inference(cnf_transformation,[],[f82]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1583,plain,
% 3.31/1.05      ( k1_xboole_0 = X0
% 3.31/1.05      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2182,plain,
% 3.31/1.05      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_11,c_1583]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_2899,plain,
% 3.31/1.05      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_2797,c_2182]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10513,plain,
% 3.31/1.05      ( sK3 = k1_xboole_0 ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_10508,c_2899]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_15188,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.31/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.31/1.05      inference(light_normalisation,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_6815,c_3241,c_9731,c_10513]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_8,plain,
% 3.31/1.05      ( r1_tarski(X0,X0) ),
% 3.31/1.05      inference(cnf_transformation,[],[f108]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1587,plain,
% 3.31/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_15192,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.31/1.05      | r2_hidden(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.31/1.05      inference(forward_subsumption_resolution,
% 3.31/1.05                [status(thm)],
% 3.31/1.05                [c_15188,c_1587]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_15195,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.31/1.05      inference(superposition,[status(thm)],[c_15192,c_1592]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_1570,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK4,sK5),k1_funct_2(sK3,sK4)) != iProver_top ),
% 3.31/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_9753,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,sK4,k1_xboole_0),k1_funct_2(sK3,sK4)) != iProver_top ),
% 3.31/1.05      inference(demodulation,[status(thm)],[c_9731,c_1570]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10199,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(sK3,k1_xboole_0,k1_xboole_0),k1_funct_2(sK3,k1_xboole_0)) != iProver_top ),
% 3.31/1.05      inference(demodulation,[status(thm)],[c_10192,c_9753]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(c_10744,plain,
% 3.31/1.05      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.31/1.05      inference(demodulation,[status(thm)],[c_10513,c_10199]) ).
% 3.31/1.05  
% 3.31/1.05  cnf(contradiction,plain,
% 3.31/1.05      ( $false ),
% 3.31/1.05      inference(minisat,[status(thm)],[c_15195,c_10744]) ).
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.05  
% 3.31/1.05  ------                               Statistics
% 3.31/1.05  
% 3.31/1.05  ------ General
% 3.31/1.05  
% 3.31/1.05  abstr_ref_over_cycles:                  0
% 3.31/1.05  abstr_ref_under_cycles:                 0
% 3.31/1.05  gc_basic_clause_elim:                   0
% 3.31/1.05  forced_gc_time:                         0
% 3.31/1.05  parsing_time:                           0.008
% 3.31/1.05  unif_index_cands_time:                  0.
% 3.31/1.05  unif_index_add_time:                    0.
% 3.31/1.05  orderings_time:                         0.
% 3.31/1.05  out_proof_time:                         0.011
% 3.31/1.05  total_time:                             0.321
% 3.31/1.05  num_of_symbols:                         51
% 3.31/1.05  num_of_terms:                           11189
% 3.31/1.05  
% 3.31/1.05  ------ Preprocessing
% 3.31/1.05  
% 3.31/1.05  num_of_splits:                          0
% 3.31/1.05  num_of_split_atoms:                     0
% 3.31/1.05  num_of_reused_defs:                     0
% 3.31/1.05  num_eq_ax_congr_red:                    20
% 3.31/1.05  num_of_sem_filtered_clauses:            1
% 3.31/1.05  num_of_subtypes:                        0
% 3.31/1.05  monotx_restored_types:                  0
% 3.31/1.05  sat_num_of_epr_types:                   0
% 3.31/1.05  sat_num_of_non_cyclic_types:            0
% 3.31/1.05  sat_guarded_non_collapsed_types:        0
% 3.31/1.05  num_pure_diseq_elim:                    0
% 3.31/1.05  simp_replaced_by:                       0
% 3.31/1.05  res_preprocessed:                       163
% 3.31/1.05  prep_upred:                             0
% 3.31/1.05  prep_unflattend:                        6
% 3.31/1.05  smt_new_axioms:                         0
% 3.31/1.05  pred_elim_cands:                        5
% 3.31/1.05  pred_elim:                              3
% 3.31/1.05  pred_elim_cl:                           4
% 3.31/1.05  pred_elim_cycles:                       6
% 3.31/1.05  merged_defs:                            8
% 3.31/1.05  merged_defs_ncl:                        0
% 3.31/1.05  bin_hyper_res:                          8
% 3.31/1.05  prep_cycles:                            4
% 3.31/1.05  pred_elim_time:                         0.004
% 3.31/1.05  splitting_time:                         0.
% 3.31/1.05  sem_filter_time:                        0.
% 3.31/1.05  monotx_time:                            0.
% 3.31/1.05  subtype_inf_time:                       0.
% 3.31/1.05  
% 3.31/1.05  ------ Problem properties
% 3.31/1.05  
% 3.31/1.05  clauses:                                34
% 3.31/1.05  conjectures:                            3
% 3.31/1.05  epr:                                    8
% 3.31/1.05  horn:                                   28
% 3.31/1.05  ground:                                 4
% 3.31/1.05  unary:                                  9
% 3.31/1.05  binary:                                 11
% 3.31/1.05  lits:                                   81
% 3.31/1.05  lits_eq:                                9
% 3.31/1.05  fd_pure:                                0
% 3.31/1.05  fd_pseudo:                              0
% 3.31/1.05  fd_cond:                                4
% 3.31/1.05  fd_pseudo_cond:                         1
% 3.31/1.05  ac_symbols:                             0
% 3.31/1.05  
% 3.31/1.05  ------ Propositional Solver
% 3.31/1.05  
% 3.31/1.05  prop_solver_calls:                      28
% 3.31/1.05  prop_fast_solver_calls:                 1422
% 3.31/1.05  smt_solver_calls:                       0
% 3.31/1.05  smt_fast_solver_calls:                  0
% 3.31/1.05  prop_num_of_clauses:                    5046
% 3.31/1.05  prop_preprocess_simplified:             12391
% 3.31/1.05  prop_fo_subsumed:                       65
% 3.31/1.05  prop_solver_time:                       0.
% 3.31/1.05  smt_solver_time:                        0.
% 3.31/1.05  smt_fast_solver_time:                   0.
% 3.31/1.05  prop_fast_solver_time:                  0.
% 3.31/1.05  prop_unsat_core_time:                   0.
% 3.31/1.05  
% 3.31/1.05  ------ QBF
% 3.31/1.05  
% 3.31/1.05  qbf_q_res:                              0
% 3.31/1.05  qbf_num_tautologies:                    0
% 3.31/1.05  qbf_prep_cycles:                        0
% 3.31/1.05  
% 3.31/1.05  ------ BMC1
% 3.31/1.05  
% 3.31/1.05  bmc1_current_bound:                     -1
% 3.31/1.05  bmc1_last_solved_bound:                 -1
% 3.31/1.05  bmc1_unsat_core_size:                   -1
% 3.31/1.05  bmc1_unsat_core_parents_size:           -1
% 3.31/1.05  bmc1_merge_next_fun:                    0
% 3.31/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.31/1.05  
% 3.31/1.05  ------ Instantiation
% 3.31/1.05  
% 3.31/1.05  inst_num_of_clauses:                    1349
% 3.31/1.05  inst_num_in_passive:                    158
% 3.31/1.05  inst_num_in_active:                     607
% 3.31/1.05  inst_num_in_unprocessed:                586
% 3.31/1.05  inst_num_of_loops:                      690
% 3.31/1.05  inst_num_of_learning_restarts:          0
% 3.31/1.05  inst_num_moves_active_passive:          81
% 3.31/1.05  inst_lit_activity:                      0
% 3.31/1.05  inst_lit_activity_moves:                0
% 3.31/1.05  inst_num_tautologies:                   0
% 3.31/1.05  inst_num_prop_implied:                  0
% 3.31/1.05  inst_num_existing_simplified:           0
% 3.31/1.05  inst_num_eq_res_simplified:             0
% 3.31/1.05  inst_num_child_elim:                    0
% 3.31/1.05  inst_num_of_dismatching_blockings:      763
% 3.31/1.05  inst_num_of_non_proper_insts:           1771
% 3.31/1.05  inst_num_of_duplicates:                 0
% 3.31/1.05  inst_inst_num_from_inst_to_res:         0
% 3.31/1.05  inst_dismatching_checking_time:         0.
% 3.31/1.05  
% 3.31/1.05  ------ Resolution
% 3.31/1.05  
% 3.31/1.05  res_num_of_clauses:                     0
% 3.31/1.05  res_num_in_passive:                     0
% 3.31/1.05  res_num_in_active:                      0
% 3.31/1.05  res_num_of_loops:                       167
% 3.31/1.05  res_forward_subset_subsumed:            169
% 3.31/1.05  res_backward_subset_subsumed:           12
% 3.31/1.05  res_forward_subsumed:                   0
% 3.31/1.05  res_backward_subsumed:                  0
% 3.31/1.05  res_forward_subsumption_resolution:     4
% 3.31/1.05  res_backward_subsumption_resolution:    0
% 3.31/1.05  res_clause_to_clause_subsumption:       1093
% 3.31/1.05  res_orphan_elimination:                 0
% 3.31/1.05  res_tautology_del:                      167
% 3.31/1.05  res_num_eq_res_simplified:              0
% 3.31/1.05  res_num_sel_changes:                    0
% 3.31/1.05  res_moves_from_active_to_pass:          0
% 3.31/1.05  
% 3.31/1.05  ------ Superposition
% 3.31/1.05  
% 3.31/1.05  sup_time_total:                         0.
% 3.31/1.05  sup_time_generating:                    0.
% 3.31/1.05  sup_time_sim_full:                      0.
% 3.31/1.05  sup_time_sim_immed:                     0.
% 3.31/1.05  
% 3.31/1.05  sup_num_of_clauses:                     241
% 3.31/1.05  sup_num_in_active:                      86
% 3.31/1.05  sup_num_in_passive:                     155
% 3.31/1.05  sup_num_of_loops:                       136
% 3.31/1.05  sup_fw_superposition:                   255
% 3.31/1.05  sup_bw_superposition:                   161
% 3.31/1.05  sup_immediate_simplified:               81
% 3.31/1.05  sup_given_eliminated:                   2
% 3.31/1.05  comparisons_done:                       0
% 3.31/1.05  comparisons_avoided:                    0
% 3.31/1.05  
% 3.31/1.05  ------ Simplifications
% 3.31/1.05  
% 3.31/1.05  
% 3.31/1.05  sim_fw_subset_subsumed:                 33
% 3.31/1.05  sim_bw_subset_subsumed:                 11
% 3.31/1.05  sim_fw_subsumed:                        38
% 3.31/1.05  sim_bw_subsumed:                        1
% 3.31/1.05  sim_fw_subsumption_res:                 6
% 3.31/1.05  sim_bw_subsumption_res:                 0
% 3.31/1.05  sim_tautology_del:                      24
% 3.31/1.05  sim_eq_tautology_del:                   17
% 3.31/1.05  sim_eq_res_simp:                        0
% 3.31/1.05  sim_fw_demodulated:                     26
% 3.31/1.05  sim_bw_demodulated:                     51
% 3.31/1.05  sim_light_normalised:                   74
% 3.31/1.05  sim_joinable_taut:                      0
% 3.31/1.05  sim_joinable_simp:                      0
% 3.31/1.05  sim_ac_normalised:                      0
% 3.31/1.05  sim_smt_subsumption:                    0
% 3.31/1.05  
%------------------------------------------------------------------------------
