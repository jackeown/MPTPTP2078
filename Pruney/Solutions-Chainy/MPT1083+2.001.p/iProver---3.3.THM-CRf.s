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
% DateTime   : Thu Dec  3 12:10:27 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 522 expanded)
%              Number of clauses        :   73 ( 137 expanded)
%              Number of leaves         :   17 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  489 (3307 expanded)
%              Number of equality atoms :  141 ( 532 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,X1))
        & v1_funct_1(sK3)
        & v5_relat_1(sK3,X0)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
     => ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK2))
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,sK1)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X1,sK1,sK1)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2))
    & v1_funct_1(sK3)
    & v5_relat_1(sK3,sK1)
    & v1_relat_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f43,f42,f41])).

fof(f76,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f39])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f68])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( v5_relat_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_396,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_397,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_29,c_27])).

cnf(c_3546,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_20,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3558,plain,
    ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5091,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3546,c_3558])).

cnf(c_38,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3823,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4587,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3823])).

cnf(c_4588,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4587])).

cnf(c_5426,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5091,c_38,c_40,c_4588])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3559,plain,
    ( k8_relset_1(X0,X1,X2,X1) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5434,plain,
    ( k8_relset_1(k1_relat_1(sK3),sK1,sK3,sK1) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5426,c_3559])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3561,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5435,plain,
    ( k8_relset_1(k1_relat_1(sK3),sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_5426,c_3561])).

cnf(c_5439,plain,
    ( k10_relat_1(sK3,sK1) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5434,c_5435])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3556,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4564,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3546,c_3556])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3831,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
    | r2_hidden(sK0(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4833,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1)
    | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3831])).

cnf(c_4836,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4833])).

cnf(c_5360,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4564,c_38,c_40,c_4836])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3552,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4177,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_3567])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3931,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3762])).

cnf(c_3932,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3931])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3966,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3967,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3966])).

cnf(c_4241,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4177,c_37,c_3932,c_3967])).

cnf(c_3553,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3565,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4403,plain,
    ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3553,c_3565])).

cnf(c_4609,plain,
    ( k10_relat_1(sK3,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_4241,c_4403])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_17])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_425,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_9])).

cnf(c_3545,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_3919,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_3545])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1
    | sK1 != X1
    | sK1 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_425,c_31])).

cnf(c_562,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_564,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_33,c_32,c_30])).

cnf(c_4065,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3919,c_33,c_32,c_30,c_562,c_3931,c_3966])).

cnf(c_4611,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = k10_relat_1(sK3,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4609,c_4065])).

cnf(c_26,negated_conjecture,
    ( k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4650,plain,
    ( k10_relat_1(sK3,sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4611,c_26])).

cnf(c_3095,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3772,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_3095])).

cnf(c_3774,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5439,c_5360,c_4650,c_3774,c_0,c_40,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.32/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/0.93  
% 2.32/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.93  
% 2.32/0.93  ------  iProver source info
% 2.32/0.93  
% 2.32/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.93  git: non_committed_changes: false
% 2.32/0.93  git: last_make_outside_of_git: false
% 2.32/0.93  
% 2.32/0.93  ------ 
% 2.32/0.93  
% 2.32/0.93  ------ Input Options
% 2.32/0.93  
% 2.32/0.93  --out_options                           all
% 2.32/0.93  --tptp_safe_out                         true
% 2.32/0.93  --problem_path                          ""
% 2.32/0.93  --include_path                          ""
% 2.32/0.93  --clausifier                            res/vclausify_rel
% 2.32/0.93  --clausifier_options                    --mode clausify
% 2.32/0.93  --stdin                                 false
% 2.32/0.93  --stats_out                             all
% 2.32/0.93  
% 2.32/0.93  ------ General Options
% 2.32/0.93  
% 2.32/0.93  --fof                                   false
% 2.32/0.93  --time_out_real                         305.
% 2.32/0.93  --time_out_virtual                      -1.
% 2.32/0.93  --symbol_type_check                     false
% 2.32/0.93  --clausify_out                          false
% 2.32/0.93  --sig_cnt_out                           false
% 2.32/0.93  --trig_cnt_out                          false
% 2.32/0.93  --trig_cnt_out_tolerance                1.
% 2.32/0.93  --trig_cnt_out_sk_spl                   false
% 2.32/0.93  --abstr_cl_out                          false
% 2.32/0.93  
% 2.32/0.93  ------ Global Options
% 2.32/0.93  
% 2.32/0.93  --schedule                              default
% 2.32/0.93  --add_important_lit                     false
% 2.32/0.93  --prop_solver_per_cl                    1000
% 2.32/0.93  --min_unsat_core                        false
% 2.32/0.93  --soft_assumptions                      false
% 2.32/0.93  --soft_lemma_size                       3
% 2.32/0.93  --prop_impl_unit_size                   0
% 2.32/0.93  --prop_impl_unit                        []
% 2.32/0.93  --share_sel_clauses                     true
% 2.32/0.93  --reset_solvers                         false
% 2.32/0.93  --bc_imp_inh                            [conj_cone]
% 2.32/0.93  --conj_cone_tolerance                   3.
% 2.32/0.93  --extra_neg_conj                        none
% 2.32/0.93  --large_theory_mode                     true
% 2.32/0.93  --prolific_symb_bound                   200
% 2.32/0.93  --lt_threshold                          2000
% 2.32/0.93  --clause_weak_htbl                      true
% 2.32/0.93  --gc_record_bc_elim                     false
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing Options
% 2.32/0.93  
% 2.32/0.93  --preprocessing_flag                    true
% 2.32/0.93  --time_out_prep_mult                    0.1
% 2.32/0.93  --splitting_mode                        input
% 2.32/0.93  --splitting_grd                         true
% 2.32/0.93  --splitting_cvd                         false
% 2.32/0.93  --splitting_cvd_svl                     false
% 2.32/0.93  --splitting_nvd                         32
% 2.32/0.93  --sub_typing                            true
% 2.32/0.93  --prep_gs_sim                           true
% 2.32/0.93  --prep_unflatten                        true
% 2.32/0.93  --prep_res_sim                          true
% 2.32/0.93  --prep_upred                            true
% 2.32/0.93  --prep_sem_filter                       exhaustive
% 2.32/0.93  --prep_sem_filter_out                   false
% 2.32/0.93  --pred_elim                             true
% 2.32/0.93  --res_sim_input                         true
% 2.32/0.93  --eq_ax_congr_red                       true
% 2.32/0.93  --pure_diseq_elim                       true
% 2.32/0.93  --brand_transform                       false
% 2.32/0.93  --non_eq_to_eq                          false
% 2.32/0.93  --prep_def_merge                        true
% 2.32/0.93  --prep_def_merge_prop_impl              false
% 2.32/0.93  --prep_def_merge_mbd                    true
% 2.32/0.93  --prep_def_merge_tr_red                 false
% 2.32/0.93  --prep_def_merge_tr_cl                  false
% 2.32/0.93  --smt_preprocessing                     true
% 2.32/0.93  --smt_ac_axioms                         fast
% 2.32/0.93  --preprocessed_out                      false
% 2.32/0.93  --preprocessed_stats                    false
% 2.32/0.93  
% 2.32/0.93  ------ Abstraction refinement Options
% 2.32/0.93  
% 2.32/0.93  --abstr_ref                             []
% 2.32/0.93  --abstr_ref_prep                        false
% 2.32/0.93  --abstr_ref_until_sat                   false
% 2.32/0.93  --abstr_ref_sig_restrict                funpre
% 2.32/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.93  --abstr_ref_under                       []
% 2.32/0.93  
% 2.32/0.93  ------ SAT Options
% 2.32/0.93  
% 2.32/0.93  --sat_mode                              false
% 2.32/0.93  --sat_fm_restart_options                ""
% 2.32/0.93  --sat_gr_def                            false
% 2.32/0.93  --sat_epr_types                         true
% 2.32/0.93  --sat_non_cyclic_types                  false
% 2.32/0.93  --sat_finite_models                     false
% 2.32/0.93  --sat_fm_lemmas                         false
% 2.32/0.93  --sat_fm_prep                           false
% 2.32/0.93  --sat_fm_uc_incr                        true
% 2.32/0.93  --sat_out_model                         small
% 2.32/0.93  --sat_out_clauses                       false
% 2.32/0.93  
% 2.32/0.93  ------ QBF Options
% 2.32/0.93  
% 2.32/0.93  --qbf_mode                              false
% 2.32/0.93  --qbf_elim_univ                         false
% 2.32/0.93  --qbf_dom_inst                          none
% 2.32/0.93  --qbf_dom_pre_inst                      false
% 2.32/0.93  --qbf_sk_in                             false
% 2.32/0.93  --qbf_pred_elim                         true
% 2.32/0.93  --qbf_split                             512
% 2.32/0.93  
% 2.32/0.93  ------ BMC1 Options
% 2.32/0.93  
% 2.32/0.93  --bmc1_incremental                      false
% 2.32/0.93  --bmc1_axioms                           reachable_all
% 2.32/0.93  --bmc1_min_bound                        0
% 2.32/0.93  --bmc1_max_bound                        -1
% 2.32/0.93  --bmc1_max_bound_default                -1
% 2.32/0.93  --bmc1_symbol_reachability              true
% 2.32/0.93  --bmc1_property_lemmas                  false
% 2.32/0.93  --bmc1_k_induction                      false
% 2.32/0.93  --bmc1_non_equiv_states                 false
% 2.32/0.93  --bmc1_deadlock                         false
% 2.32/0.93  --bmc1_ucm                              false
% 2.32/0.93  --bmc1_add_unsat_core                   none
% 2.32/0.93  --bmc1_unsat_core_children              false
% 2.32/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.93  --bmc1_out_stat                         full
% 2.32/0.93  --bmc1_ground_init                      false
% 2.32/0.93  --bmc1_pre_inst_next_state              false
% 2.32/0.93  --bmc1_pre_inst_state                   false
% 2.32/0.93  --bmc1_pre_inst_reach_state             false
% 2.32/0.93  --bmc1_out_unsat_core                   false
% 2.32/0.93  --bmc1_aig_witness_out                  false
% 2.32/0.93  --bmc1_verbose                          false
% 2.32/0.93  --bmc1_dump_clauses_tptp                false
% 2.32/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.93  --bmc1_dump_file                        -
% 2.32/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.93  --bmc1_ucm_extend_mode                  1
% 2.32/0.93  --bmc1_ucm_init_mode                    2
% 2.32/0.93  --bmc1_ucm_cone_mode                    none
% 2.32/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.93  --bmc1_ucm_relax_model                  4
% 2.32/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.93  --bmc1_ucm_layered_model                none
% 2.32/0.93  --bmc1_ucm_max_lemma_size               10
% 2.32/0.93  
% 2.32/0.93  ------ AIG Options
% 2.32/0.93  
% 2.32/0.93  --aig_mode                              false
% 2.32/0.93  
% 2.32/0.93  ------ Instantiation Options
% 2.32/0.93  
% 2.32/0.93  --instantiation_flag                    true
% 2.32/0.93  --inst_sos_flag                         false
% 2.32/0.93  --inst_sos_phase                        true
% 2.32/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.93  --inst_lit_sel_side                     num_symb
% 2.32/0.93  --inst_solver_per_active                1400
% 2.32/0.93  --inst_solver_calls_frac                1.
% 2.32/0.93  --inst_passive_queue_type               priority_queues
% 2.32/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.93  --inst_passive_queues_freq              [25;2]
% 2.32/0.93  --inst_dismatching                      true
% 2.32/0.93  --inst_eager_unprocessed_to_passive     true
% 2.32/0.93  --inst_prop_sim_given                   true
% 2.32/0.93  --inst_prop_sim_new                     false
% 2.32/0.93  --inst_subs_new                         false
% 2.32/0.93  --inst_eq_res_simp                      false
% 2.32/0.93  --inst_subs_given                       false
% 2.32/0.93  --inst_orphan_elimination               true
% 2.32/0.93  --inst_learning_loop_flag               true
% 2.32/0.93  --inst_learning_start                   3000
% 2.32/0.93  --inst_learning_factor                  2
% 2.32/0.93  --inst_start_prop_sim_after_learn       3
% 2.32/0.93  --inst_sel_renew                        solver
% 2.32/0.93  --inst_lit_activity_flag                true
% 2.32/0.93  --inst_restr_to_given                   false
% 2.32/0.93  --inst_activity_threshold               500
% 2.32/0.93  --inst_out_proof                        true
% 2.32/0.93  
% 2.32/0.93  ------ Resolution Options
% 2.32/0.93  
% 2.32/0.93  --resolution_flag                       true
% 2.32/0.93  --res_lit_sel                           adaptive
% 2.32/0.93  --res_lit_sel_side                      none
% 2.32/0.93  --res_ordering                          kbo
% 2.32/0.93  --res_to_prop_solver                    active
% 2.32/0.93  --res_prop_simpl_new                    false
% 2.32/0.93  --res_prop_simpl_given                  true
% 2.32/0.93  --res_passive_queue_type                priority_queues
% 2.32/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.93  --res_passive_queues_freq               [15;5]
% 2.32/0.93  --res_forward_subs                      full
% 2.32/0.93  --res_backward_subs                     full
% 2.32/0.93  --res_forward_subs_resolution           true
% 2.32/0.93  --res_backward_subs_resolution          true
% 2.32/0.93  --res_orphan_elimination                true
% 2.32/0.93  --res_time_limit                        2.
% 2.32/0.93  --res_out_proof                         true
% 2.32/0.93  
% 2.32/0.93  ------ Superposition Options
% 2.32/0.93  
% 2.32/0.93  --superposition_flag                    true
% 2.32/0.93  --sup_passive_queue_type                priority_queues
% 2.32/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.93  --demod_completeness_check              fast
% 2.32/0.93  --demod_use_ground                      true
% 2.32/0.93  --sup_to_prop_solver                    passive
% 2.32/0.93  --sup_prop_simpl_new                    true
% 2.32/0.93  --sup_prop_simpl_given                  true
% 2.32/0.93  --sup_fun_splitting                     false
% 2.32/0.93  --sup_smt_interval                      50000
% 2.32/0.93  
% 2.32/0.93  ------ Superposition Simplification Setup
% 2.32/0.93  
% 2.32/0.93  --sup_indices_passive                   []
% 2.32/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_full_bw                           [BwDemod]
% 2.32/0.93  --sup_immed_triv                        [TrivRules]
% 2.32/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_immed_bw_main                     []
% 2.32/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.93  
% 2.32/0.93  ------ Combination Options
% 2.32/0.93  
% 2.32/0.93  --comb_res_mult                         3
% 2.32/0.93  --comb_sup_mult                         2
% 2.32/0.93  --comb_inst_mult                        10
% 2.32/0.93  
% 2.32/0.93  ------ Debug Options
% 2.32/0.93  
% 2.32/0.93  --dbg_backtrace                         false
% 2.32/0.93  --dbg_dump_prop_clauses                 false
% 2.32/0.93  --dbg_dump_prop_clauses_file            -
% 2.32/0.93  --dbg_out_stat                          false
% 2.32/0.93  ------ Parsing...
% 2.32/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.93  ------ Proving...
% 2.32/0.93  ------ Problem Properties 
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  clauses                                 25
% 2.32/0.93  conjectures                             7
% 2.32/0.93  EPR                                     7
% 2.32/0.93  Horn                                    20
% 2.32/0.93  unary                                   9
% 2.32/0.93  binary                                  3
% 2.32/0.93  lits                                    68
% 2.32/0.93  lits eq                                 11
% 2.32/0.93  fd_pure                                 0
% 2.32/0.93  fd_pseudo                               0
% 2.32/0.93  fd_cond                                 2
% 2.32/0.93  fd_pseudo_cond                          1
% 2.32/0.93  AC symbols                              0
% 2.32/0.93  
% 2.32/0.93  ------ Schedule dynamic 5 is on 
% 2.32/0.93  
% 2.32/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  ------ 
% 2.32/0.93  Current options:
% 2.32/0.93  ------ 
% 2.32/0.93  
% 2.32/0.93  ------ Input Options
% 2.32/0.93  
% 2.32/0.93  --out_options                           all
% 2.32/0.93  --tptp_safe_out                         true
% 2.32/0.93  --problem_path                          ""
% 2.32/0.93  --include_path                          ""
% 2.32/0.93  --clausifier                            res/vclausify_rel
% 2.32/0.93  --clausifier_options                    --mode clausify
% 2.32/0.93  --stdin                                 false
% 2.32/0.93  --stats_out                             all
% 2.32/0.93  
% 2.32/0.93  ------ General Options
% 2.32/0.93  
% 2.32/0.93  --fof                                   false
% 2.32/0.93  --time_out_real                         305.
% 2.32/0.93  --time_out_virtual                      -1.
% 2.32/0.93  --symbol_type_check                     false
% 2.32/0.93  --clausify_out                          false
% 2.32/0.93  --sig_cnt_out                           false
% 2.32/0.93  --trig_cnt_out                          false
% 2.32/0.93  --trig_cnt_out_tolerance                1.
% 2.32/0.93  --trig_cnt_out_sk_spl                   false
% 2.32/0.93  --abstr_cl_out                          false
% 2.32/0.93  
% 2.32/0.93  ------ Global Options
% 2.32/0.93  
% 2.32/0.93  --schedule                              default
% 2.32/0.93  --add_important_lit                     false
% 2.32/0.93  --prop_solver_per_cl                    1000
% 2.32/0.93  --min_unsat_core                        false
% 2.32/0.93  --soft_assumptions                      false
% 2.32/0.93  --soft_lemma_size                       3
% 2.32/0.93  --prop_impl_unit_size                   0
% 2.32/0.93  --prop_impl_unit                        []
% 2.32/0.93  --share_sel_clauses                     true
% 2.32/0.93  --reset_solvers                         false
% 2.32/0.93  --bc_imp_inh                            [conj_cone]
% 2.32/0.93  --conj_cone_tolerance                   3.
% 2.32/0.93  --extra_neg_conj                        none
% 2.32/0.93  --large_theory_mode                     true
% 2.32/0.93  --prolific_symb_bound                   200
% 2.32/0.93  --lt_threshold                          2000
% 2.32/0.93  --clause_weak_htbl                      true
% 2.32/0.93  --gc_record_bc_elim                     false
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing Options
% 2.32/0.93  
% 2.32/0.93  --preprocessing_flag                    true
% 2.32/0.93  --time_out_prep_mult                    0.1
% 2.32/0.93  --splitting_mode                        input
% 2.32/0.93  --splitting_grd                         true
% 2.32/0.93  --splitting_cvd                         false
% 2.32/0.93  --splitting_cvd_svl                     false
% 2.32/0.93  --splitting_nvd                         32
% 2.32/0.93  --sub_typing                            true
% 2.32/0.93  --prep_gs_sim                           true
% 2.32/0.93  --prep_unflatten                        true
% 2.32/0.93  --prep_res_sim                          true
% 2.32/0.93  --prep_upred                            true
% 2.32/0.93  --prep_sem_filter                       exhaustive
% 2.32/0.93  --prep_sem_filter_out                   false
% 2.32/0.93  --pred_elim                             true
% 2.32/0.93  --res_sim_input                         true
% 2.32/0.93  --eq_ax_congr_red                       true
% 2.32/0.93  --pure_diseq_elim                       true
% 2.32/0.93  --brand_transform                       false
% 2.32/0.93  --non_eq_to_eq                          false
% 2.32/0.93  --prep_def_merge                        true
% 2.32/0.93  --prep_def_merge_prop_impl              false
% 2.32/0.93  --prep_def_merge_mbd                    true
% 2.32/0.93  --prep_def_merge_tr_red                 false
% 2.32/0.93  --prep_def_merge_tr_cl                  false
% 2.32/0.93  --smt_preprocessing                     true
% 2.32/0.93  --smt_ac_axioms                         fast
% 2.32/0.93  --preprocessed_out                      false
% 2.32/0.93  --preprocessed_stats                    false
% 2.32/0.93  
% 2.32/0.93  ------ Abstraction refinement Options
% 2.32/0.93  
% 2.32/0.93  --abstr_ref                             []
% 2.32/0.93  --abstr_ref_prep                        false
% 2.32/0.93  --abstr_ref_until_sat                   false
% 2.32/0.93  --abstr_ref_sig_restrict                funpre
% 2.32/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.93  --abstr_ref_under                       []
% 2.32/0.93  
% 2.32/0.93  ------ SAT Options
% 2.32/0.93  
% 2.32/0.93  --sat_mode                              false
% 2.32/0.93  --sat_fm_restart_options                ""
% 2.32/0.93  --sat_gr_def                            false
% 2.32/0.93  --sat_epr_types                         true
% 2.32/0.93  --sat_non_cyclic_types                  false
% 2.32/0.93  --sat_finite_models                     false
% 2.32/0.93  --sat_fm_lemmas                         false
% 2.32/0.93  --sat_fm_prep                           false
% 2.32/0.93  --sat_fm_uc_incr                        true
% 2.32/0.93  --sat_out_model                         small
% 2.32/0.93  --sat_out_clauses                       false
% 2.32/0.93  
% 2.32/0.93  ------ QBF Options
% 2.32/0.93  
% 2.32/0.93  --qbf_mode                              false
% 2.32/0.93  --qbf_elim_univ                         false
% 2.32/0.93  --qbf_dom_inst                          none
% 2.32/0.93  --qbf_dom_pre_inst                      false
% 2.32/0.93  --qbf_sk_in                             false
% 2.32/0.93  --qbf_pred_elim                         true
% 2.32/0.93  --qbf_split                             512
% 2.32/0.93  
% 2.32/0.93  ------ BMC1 Options
% 2.32/0.93  
% 2.32/0.93  --bmc1_incremental                      false
% 2.32/0.93  --bmc1_axioms                           reachable_all
% 2.32/0.93  --bmc1_min_bound                        0
% 2.32/0.93  --bmc1_max_bound                        -1
% 2.32/0.93  --bmc1_max_bound_default                -1
% 2.32/0.93  --bmc1_symbol_reachability              true
% 2.32/0.93  --bmc1_property_lemmas                  false
% 2.32/0.93  --bmc1_k_induction                      false
% 2.32/0.93  --bmc1_non_equiv_states                 false
% 2.32/0.93  --bmc1_deadlock                         false
% 2.32/0.93  --bmc1_ucm                              false
% 2.32/0.93  --bmc1_add_unsat_core                   none
% 2.32/0.93  --bmc1_unsat_core_children              false
% 2.32/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.93  --bmc1_out_stat                         full
% 2.32/0.93  --bmc1_ground_init                      false
% 2.32/0.93  --bmc1_pre_inst_next_state              false
% 2.32/0.93  --bmc1_pre_inst_state                   false
% 2.32/0.93  --bmc1_pre_inst_reach_state             false
% 2.32/0.93  --bmc1_out_unsat_core                   false
% 2.32/0.93  --bmc1_aig_witness_out                  false
% 2.32/0.93  --bmc1_verbose                          false
% 2.32/0.93  --bmc1_dump_clauses_tptp                false
% 2.32/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.93  --bmc1_dump_file                        -
% 2.32/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.93  --bmc1_ucm_extend_mode                  1
% 2.32/0.93  --bmc1_ucm_init_mode                    2
% 2.32/0.93  --bmc1_ucm_cone_mode                    none
% 2.32/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.93  --bmc1_ucm_relax_model                  4
% 2.32/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.93  --bmc1_ucm_layered_model                none
% 2.32/0.93  --bmc1_ucm_max_lemma_size               10
% 2.32/0.93  
% 2.32/0.93  ------ AIG Options
% 2.32/0.93  
% 2.32/0.93  --aig_mode                              false
% 2.32/0.93  
% 2.32/0.93  ------ Instantiation Options
% 2.32/0.93  
% 2.32/0.93  --instantiation_flag                    true
% 2.32/0.93  --inst_sos_flag                         false
% 2.32/0.93  --inst_sos_phase                        true
% 2.32/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.93  --inst_lit_sel_side                     none
% 2.32/0.93  --inst_solver_per_active                1400
% 2.32/0.93  --inst_solver_calls_frac                1.
% 2.32/0.93  --inst_passive_queue_type               priority_queues
% 2.32/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.93  --inst_passive_queues_freq              [25;2]
% 2.32/0.93  --inst_dismatching                      true
% 2.32/0.93  --inst_eager_unprocessed_to_passive     true
% 2.32/0.93  --inst_prop_sim_given                   true
% 2.32/0.93  --inst_prop_sim_new                     false
% 2.32/0.93  --inst_subs_new                         false
% 2.32/0.93  --inst_eq_res_simp                      false
% 2.32/0.93  --inst_subs_given                       false
% 2.32/0.93  --inst_orphan_elimination               true
% 2.32/0.93  --inst_learning_loop_flag               true
% 2.32/0.93  --inst_learning_start                   3000
% 2.32/0.93  --inst_learning_factor                  2
% 2.32/0.93  --inst_start_prop_sim_after_learn       3
% 2.32/0.93  --inst_sel_renew                        solver
% 2.32/0.93  --inst_lit_activity_flag                true
% 2.32/0.93  --inst_restr_to_given                   false
% 2.32/0.93  --inst_activity_threshold               500
% 2.32/0.93  --inst_out_proof                        true
% 2.32/0.93  
% 2.32/0.93  ------ Resolution Options
% 2.32/0.93  
% 2.32/0.93  --resolution_flag                       false
% 2.32/0.93  --res_lit_sel                           adaptive
% 2.32/0.93  --res_lit_sel_side                      none
% 2.32/0.93  --res_ordering                          kbo
% 2.32/0.93  --res_to_prop_solver                    active
% 2.32/0.93  --res_prop_simpl_new                    false
% 2.32/0.93  --res_prop_simpl_given                  true
% 2.32/0.93  --res_passive_queue_type                priority_queues
% 2.32/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.93  --res_passive_queues_freq               [15;5]
% 2.32/0.93  --res_forward_subs                      full
% 2.32/0.93  --res_backward_subs                     full
% 2.32/0.93  --res_forward_subs_resolution           true
% 2.32/0.93  --res_backward_subs_resolution          true
% 2.32/0.93  --res_orphan_elimination                true
% 2.32/0.93  --res_time_limit                        2.
% 2.32/0.93  --res_out_proof                         true
% 2.32/0.93  
% 2.32/0.93  ------ Superposition Options
% 2.32/0.93  
% 2.32/0.93  --superposition_flag                    true
% 2.32/0.93  --sup_passive_queue_type                priority_queues
% 2.32/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.93  --demod_completeness_check              fast
% 2.32/0.93  --demod_use_ground                      true
% 2.32/0.93  --sup_to_prop_solver                    passive
% 2.32/0.93  --sup_prop_simpl_new                    true
% 2.32/0.93  --sup_prop_simpl_given                  true
% 2.32/0.93  --sup_fun_splitting                     false
% 2.32/0.93  --sup_smt_interval                      50000
% 2.32/0.93  
% 2.32/0.93  ------ Superposition Simplification Setup
% 2.32/0.93  
% 2.32/0.93  --sup_indices_passive                   []
% 2.32/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_full_bw                           [BwDemod]
% 2.32/0.93  --sup_immed_triv                        [TrivRules]
% 2.32/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_immed_bw_main                     []
% 2.32/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.93  
% 2.32/0.93  ------ Combination Options
% 2.32/0.93  
% 2.32/0.93  --comb_res_mult                         3
% 2.32/0.93  --comb_sup_mult                         2
% 2.32/0.93  --comb_inst_mult                        10
% 2.32/0.93  
% 2.32/0.93  ------ Debug Options
% 2.32/0.93  
% 2.32/0.93  --dbg_backtrace                         false
% 2.32/0.93  --dbg_dump_prop_clauses                 false
% 2.32/0.93  --dbg_dump_prop_clauses_file            -
% 2.32/0.93  --dbg_out_stat                          false
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  ------ Proving...
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  % SZS status Theorem for theBenchmark.p
% 2.32/0.93  
% 2.32/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.93  
% 2.32/0.93  fof(f7,axiom,(
% 2.32/0.93    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f22,plain,(
% 2.32/0.93    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.32/0.93    inference(ennf_transformation,[],[f7])).
% 2.32/0.93  
% 2.32/0.93  fof(f23,plain,(
% 2.32/0.93    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.32/0.93    inference(flattening,[],[f22])).
% 2.32/0.93  
% 2.32/0.93  fof(f52,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f23])).
% 2.32/0.93  
% 2.32/0.93  fof(f15,conjecture,(
% 2.32/0.93    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f16,negated_conjecture,(
% 2.32/0.93    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 2.32/0.93    inference(negated_conjecture,[],[f15])).
% 2.32/0.93  
% 2.32/0.93  fof(f36,plain,(
% 2.32/0.93    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 2.32/0.93    inference(ennf_transformation,[],[f16])).
% 2.32/0.93  
% 2.32/0.93  fof(f37,plain,(
% 2.32/0.93    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 2.32/0.93    inference(flattening,[],[f36])).
% 2.32/0.93  
% 2.32/0.93  fof(f43,plain,(
% 2.32/0.93    ( ! [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,X1)) & v1_funct_1(sK3) & v5_relat_1(sK3,X0) & v1_relat_1(sK3))) )),
% 2.32/0.93    introduced(choice_axiom,[])).
% 2.32/0.93  
% 2.32/0.93  fof(f42,plain,(
% 2.32/0.93    ( ! [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.32/0.93    introduced(choice_axiom,[])).
% 2.32/0.93  
% 2.32/0.93  fof(f41,plain,(
% 2.32/0.93    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK1) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X1,sK1,sK1) & v1_funct_1(X1)) & ~v1_xboole_0(sK1))),
% 2.32/0.93    introduced(choice_axiom,[])).
% 2.32/0.93  
% 2.32/0.93  fof(f44,plain,(
% 2.32/0.93    ((k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2)) & v1_funct_1(sK3) & v5_relat_1(sK3,sK1) & v1_relat_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)),
% 2.32/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f43,f42,f41])).
% 2.32/0.93  
% 2.32/0.93  fof(f76,plain,(
% 2.32/0.93    v5_relat_1(sK3,sK1)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f75,plain,(
% 2.32/0.93    v1_relat_1(sK3)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f77,plain,(
% 2.32/0.93    v1_funct_1(sK3)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f14,axiom,(
% 2.32/0.93    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f34,plain,(
% 2.32/0.93    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.32/0.93    inference(ennf_transformation,[],[f14])).
% 2.32/0.93  
% 2.32/0.93  fof(f35,plain,(
% 2.32/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.32/0.93    inference(flattening,[],[f34])).
% 2.32/0.93  
% 2.32/0.93  fof(f39,plain,(
% 2.32/0.93    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 2.32/0.93    introduced(choice_axiom,[])).
% 2.32/0.93  
% 2.32/0.93  fof(f40,plain,(
% 2.32/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.32/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f39])).
% 2.32/0.93  
% 2.32/0.93  fof(f70,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f40])).
% 2.32/0.93  
% 2.32/0.93  fof(f81,plain,(
% 2.32/0.93    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(equality_resolution,[],[f70])).
% 2.32/0.93  
% 2.32/0.93  fof(f69,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f40])).
% 2.32/0.93  
% 2.32/0.93  fof(f82,plain,(
% 2.32/0.93    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(equality_resolution,[],[f69])).
% 2.32/0.93  
% 2.32/0.93  fof(f13,axiom,(
% 2.32/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f32,plain,(
% 2.32/0.93    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.32/0.93    inference(ennf_transformation,[],[f13])).
% 2.32/0.93  
% 2.32/0.93  fof(f33,plain,(
% 2.32/0.93    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.32/0.93    inference(flattening,[],[f32])).
% 2.32/0.93  
% 2.32/0.93  fof(f63,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f33])).
% 2.32/0.93  
% 2.32/0.93  fof(f9,axiom,(
% 2.32/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f25,plain,(
% 2.32/0.93    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.93    inference(ennf_transformation,[],[f9])).
% 2.32/0.93  
% 2.32/0.93  fof(f55,plain,(
% 2.32/0.93    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.93    inference(cnf_transformation,[],[f25])).
% 2.32/0.93  
% 2.32/0.93  fof(f68,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f40])).
% 2.32/0.93  
% 2.32/0.93  fof(f83,plain,(
% 2.32/0.93    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(equality_resolution,[],[f68])).
% 2.32/0.93  
% 2.32/0.93  fof(f67,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f40])).
% 2.32/0.93  
% 2.32/0.93  fof(f84,plain,(
% 2.32/0.93    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.93    inference(equality_resolution,[],[f67])).
% 2.32/0.93  
% 2.32/0.93  fof(f74,plain,(
% 2.32/0.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f2,axiom,(
% 2.32/0.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f17,plain,(
% 2.32/0.93    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.32/0.93    inference(ennf_transformation,[],[f2])).
% 2.32/0.93  
% 2.32/0.93  fof(f46,plain,(
% 2.32/0.93    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f17])).
% 2.32/0.93  
% 2.32/0.93  fof(f3,axiom,(
% 2.32/0.93    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f47,plain,(
% 2.32/0.93    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.32/0.93    inference(cnf_transformation,[],[f3])).
% 2.32/0.93  
% 2.32/0.93  fof(f4,axiom,(
% 2.32/0.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f18,plain,(
% 2.32/0.93    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.32/0.93    inference(ennf_transformation,[],[f4])).
% 2.32/0.93  
% 2.32/0.93  fof(f48,plain,(
% 2.32/0.93    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f18])).
% 2.32/0.93  
% 2.32/0.93  fof(f10,axiom,(
% 2.32/0.93    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f26,plain,(
% 2.32/0.93    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.32/0.93    inference(ennf_transformation,[],[f10])).
% 2.32/0.93  
% 2.32/0.93  fof(f27,plain,(
% 2.32/0.93    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.32/0.93    inference(flattening,[],[f26])).
% 2.32/0.93  
% 2.32/0.93  fof(f57,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f27])).
% 2.32/0.93  
% 2.32/0.93  fof(f12,axiom,(
% 2.32/0.93    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f30,plain,(
% 2.32/0.93    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.32/0.93    inference(ennf_transformation,[],[f12])).
% 2.32/0.93  
% 2.32/0.93  fof(f31,plain,(
% 2.32/0.93    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.32/0.93    inference(flattening,[],[f30])).
% 2.32/0.93  
% 2.32/0.93  fof(f38,plain,(
% 2.32/0.93    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.32/0.93    inference(nnf_transformation,[],[f31])).
% 2.32/0.93  
% 2.32/0.93  fof(f61,plain,(
% 2.32/0.93    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.32/0.93    inference(cnf_transformation,[],[f38])).
% 2.32/0.93  
% 2.32/0.93  fof(f8,axiom,(
% 2.32/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f24,plain,(
% 2.32/0.93    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.93    inference(ennf_transformation,[],[f8])).
% 2.32/0.93  
% 2.32/0.93  fof(f53,plain,(
% 2.32/0.93    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.93    inference(cnf_transformation,[],[f24])).
% 2.32/0.93  
% 2.32/0.93  fof(f73,plain,(
% 2.32/0.93    v1_funct_2(sK2,sK1,sK1)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f71,plain,(
% 2.32/0.93    ~v1_xboole_0(sK1)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f72,plain,(
% 2.32/0.93    v1_funct_1(sK2)),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f78,plain,(
% 2.32/0.93    k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2))),
% 2.32/0.93    inference(cnf_transformation,[],[f44])).
% 2.32/0.93  
% 2.32/0.93  fof(f1,axiom,(
% 2.32/0.93    v1_xboole_0(k1_xboole_0)),
% 2.32/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.93  
% 2.32/0.93  fof(f45,plain,(
% 2.32/0.93    v1_xboole_0(k1_xboole_0)),
% 2.32/0.93    inference(cnf_transformation,[],[f1])).
% 2.32/0.93  
% 2.32/0.93  cnf(c_7,plain,
% 2.32/0.93      ( ~ v5_relat_1(X0,X1)
% 2.32/0.93      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.32/0.93      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f52]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_28,negated_conjecture,
% 2.32/0.93      ( v5_relat_1(sK3,sK1) ),
% 2.32/0.93      inference(cnf_transformation,[],[f76]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_396,plain,
% 2.32/0.93      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.32/0.93      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.32/0.93      | ~ v1_funct_1(X1)
% 2.32/0.93      | ~ v1_relat_1(X1)
% 2.32/0.93      | sK1 != X2
% 2.32/0.93      | sK3 != X1 ),
% 2.32/0.93      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_397,plain,
% 2.32/0.93      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.32/0.93      | r2_hidden(k1_funct_1(sK3,X0),sK1)
% 2.32/0.93      | ~ v1_funct_1(sK3)
% 2.32/0.93      | ~ v1_relat_1(sK3) ),
% 2.32/0.93      inference(unflattening,[status(thm)],[c_396]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_29,negated_conjecture,
% 2.32/0.93      ( v1_relat_1(sK3) ),
% 2.32/0.93      inference(cnf_transformation,[],[f75]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_27,negated_conjecture,
% 2.32/0.93      ( v1_funct_1(sK3) ),
% 2.32/0.93      inference(cnf_transformation,[],[f77]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_401,plain,
% 2.32/0.93      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.32/0.93      | r2_hidden(k1_funct_1(sK3,X0),sK1) ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_397,c_29,c_27]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3546,plain,
% 2.32/0.93      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.32/0.93      | r2_hidden(k1_funct_1(sK3,X0),sK1) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_20,plain,
% 2.32/0.93      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.32/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f81]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3558,plain,
% 2.32/0.93      ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 2.32/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 2.32/0.93      | v1_funct_1(X0) != iProver_top
% 2.32/0.93      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5091,plain,
% 2.32/0.93      ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) != iProver_top
% 2.32/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top
% 2.32/0.93      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_3546,c_3558]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_38,plain,
% 2.32/0.93      ( v1_relat_1(sK3) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_40,plain,
% 2.32/0.93      ( v1_funct_1(sK3) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_21,plain,
% 2.32/0.93      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.32/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f82]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3823,plain,
% 2.32/0.93      ( r2_hidden(sK0(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
% 2.32/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 2.32/0.93      | ~ v1_funct_1(sK3)
% 2.32/0.93      | ~ v1_relat_1(sK3) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_21]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4587,plain,
% 2.32/0.93      ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3))
% 2.32/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 2.32/0.93      | ~ v1_funct_1(sK3)
% 2.32/0.93      | ~ v1_relat_1(sK3) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_3823]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4588,plain,
% 2.32/0.93      ( r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top
% 2.32/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top
% 2.32/0.93      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_4587]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5426,plain,
% 2.32/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_5091,c_38,c_40,c_4588]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_19,plain,
% 2.32/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | k8_relset_1(X1,X2,X0,X2) = X1
% 2.32/0.93      | k1_xboole_0 = X2 ),
% 2.32/0.93      inference(cnf_transformation,[],[f63]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3559,plain,
% 2.32/0.93      ( k8_relset_1(X0,X1,X2,X1) = X0
% 2.32/0.93      | k1_xboole_0 = X1
% 2.32/0.93      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.32/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.32/0.93      | v1_funct_1(X2) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5434,plain,
% 2.32/0.93      ( k8_relset_1(k1_relat_1(sK3),sK1,sK3,sK1) = k1_relat_1(sK3)
% 2.32/0.93      | sK1 = k1_xboole_0
% 2.32/0.93      | v1_funct_2(sK3,k1_relat_1(sK3),sK1) != iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_5426,c_3559]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_10,plain,
% 2.32/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.32/0.93      inference(cnf_transformation,[],[f55]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3561,plain,
% 2.32/0.93      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.32/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5435,plain,
% 2.32/0.93      ( k8_relset_1(k1_relat_1(sK3),sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_5426,c_3561]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5439,plain,
% 2.32/0.93      ( k10_relat_1(sK3,sK1) = k1_relat_1(sK3)
% 2.32/0.93      | sK1 = k1_xboole_0
% 2.32/0.93      | v1_funct_2(sK3,k1_relat_1(sK3),sK1) != iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top ),
% 2.32/0.93      inference(demodulation,[status(thm)],[c_5434,c_5435]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_22,plain,
% 2.32/0.93      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.32/0.93      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f83]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3556,plain,
% 2.32/0.93      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 2.32/0.93      | r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 2.32/0.93      | v1_funct_1(X0) != iProver_top
% 2.32/0.93      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4564,plain,
% 2.32/0.93      ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top
% 2.32/0.93      | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) != iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top
% 2.32/0.93      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_3546,c_3556]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_23,plain,
% 2.32/0.93      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.32/0.93      | r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f84]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3831,plain,
% 2.32/0.93      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
% 2.32/0.93      | r2_hidden(sK0(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
% 2.32/0.93      | ~ v1_funct_1(sK3)
% 2.32/0.93      | ~ v1_relat_1(sK3) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_23]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4833,plain,
% 2.32/0.93      ( v1_funct_2(sK3,k1_relat_1(sK3),sK1)
% 2.32/0.93      | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3))
% 2.32/0.93      | ~ v1_funct_1(sK3)
% 2.32/0.93      | ~ v1_relat_1(sK3) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_3831]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4836,plain,
% 2.32/0.93      ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top
% 2.32/0.93      | r2_hidden(sK0(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top
% 2.32/0.93      | v1_funct_1(sK3) != iProver_top
% 2.32/0.93      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_4833]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_5360,plain,
% 2.32/0.93      ( v1_funct_2(sK3,k1_relat_1(sK3),sK1) = iProver_top ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_4564,c_38,c_40,c_4836]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_30,negated_conjecture,
% 2.32/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.32/0.93      inference(cnf_transformation,[],[f74]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3552,plain,
% 2.32/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_1,plain,
% 2.32/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/0.93      | ~ v1_relat_1(X1)
% 2.32/0.93      | v1_relat_1(X0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f46]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3567,plain,
% 2.32/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.32/0.93      | v1_relat_1(X1) != iProver_top
% 2.32/0.93      | v1_relat_1(X0) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4177,plain,
% 2.32/0.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 2.32/0.93      | v1_relat_1(sK2) = iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_3552,c_3567]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_37,plain,
% 2.32/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3762,plain,
% 2.32/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | v1_relat_1(X0)
% 2.32/0.93      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3931,plain,
% 2.32/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.32/0.93      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 2.32/0.93      | v1_relat_1(sK2) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_3762]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3932,plain,
% 2.32/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.32/0.93      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 2.32/0.93      | v1_relat_1(sK2) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_3931]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_2,plain,
% 2.32/0.93      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.32/0.93      inference(cnf_transformation,[],[f47]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3966,plain,
% 2.32/0.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3967,plain,
% 2.32/0.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_3966]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4241,plain,
% 2.32/0.93      ( v1_relat_1(sK2) = iProver_top ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_4177,c_37,c_3932,c_3967]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3553,plain,
% 2.32/0.93      ( v1_relat_1(sK3) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3,plain,
% 2.32/0.93      ( ~ v1_relat_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X1)
% 2.32/0.93      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.32/0.93      inference(cnf_transformation,[],[f48]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3565,plain,
% 2.32/0.93      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.32/0.93      | v1_relat_1(X0) != iProver_top
% 2.32/0.93      | v1_relat_1(X1) != iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4403,plain,
% 2.32/0.93      ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
% 2.32/0.93      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_3553,c_3565]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4609,plain,
% 2.32/0.93      ( k10_relat_1(sK3,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK3,sK2)) ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_4241,c_4403]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_11,plain,
% 2.32/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.93      | v1_partfun1(X0,X1)
% 2.32/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | v1_xboole_0(X2) ),
% 2.32/0.93      inference(cnf_transformation,[],[f57]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_17,plain,
% 2.32/0.93      ( ~ v1_partfun1(X0,X1)
% 2.32/0.93      | ~ v4_relat_1(X0,X1)
% 2.32/0.93      | ~ v1_relat_1(X0)
% 2.32/0.93      | k1_relat_1(X0) = X1 ),
% 2.32/0.93      inference(cnf_transformation,[],[f61]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_423,plain,
% 2.32/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.93      | ~ v4_relat_1(X0,X1)
% 2.32/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0)
% 2.32/0.93      | v1_xboole_0(X2)
% 2.32/0.93      | k1_relat_1(X0) = X1 ),
% 2.32/0.93      inference(resolution,[status(thm)],[c_11,c_17]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_9,plain,
% 2.32/0.93      ( v4_relat_1(X0,X1)
% 2.32/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.32/0.93      inference(cnf_transformation,[],[f53]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_425,plain,
% 2.32/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0)
% 2.32/0.93      | v1_xboole_0(X2)
% 2.32/0.93      | k1_relat_1(X0) = X1 ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_423,c_9]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3545,plain,
% 2.32/0.93      ( k1_relat_1(X0) = X1
% 2.32/0.93      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.32/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.32/0.93      | v1_funct_1(X0) != iProver_top
% 2.32/0.93      | v1_relat_1(X0) != iProver_top
% 2.32/0.93      | v1_xboole_0(X2) = iProver_top ),
% 2.32/0.93      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3919,plain,
% 2.32/0.93      ( k1_relat_1(sK2) = sK1
% 2.32/0.93      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.32/0.93      | v1_funct_1(sK2) != iProver_top
% 2.32/0.93      | v1_relat_1(sK2) != iProver_top
% 2.32/0.93      | v1_xboole_0(sK1) = iProver_top ),
% 2.32/0.93      inference(superposition,[status(thm)],[c_3552,c_3545]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_31,negated_conjecture,
% 2.32/0.93      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.32/0.93      inference(cnf_transformation,[],[f73]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_561,plain,
% 2.32/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.93      | ~ v1_funct_1(X0)
% 2.32/0.93      | ~ v1_relat_1(X0)
% 2.32/0.93      | v1_xboole_0(X2)
% 2.32/0.93      | k1_relat_1(X0) = X1
% 2.32/0.93      | sK1 != X1
% 2.32/0.93      | sK1 != X2
% 2.32/0.93      | sK2 != X0 ),
% 2.32/0.93      inference(resolution_lifted,[status(thm)],[c_425,c_31]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_562,plain,
% 2.32/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.32/0.93      | ~ v1_funct_1(sK2)
% 2.32/0.93      | ~ v1_relat_1(sK2)
% 2.32/0.93      | v1_xboole_0(sK1)
% 2.32/0.93      | k1_relat_1(sK2) = sK1 ),
% 2.32/0.93      inference(unflattening,[status(thm)],[c_561]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_33,negated_conjecture,
% 2.32/0.93      ( ~ v1_xboole_0(sK1) ),
% 2.32/0.93      inference(cnf_transformation,[],[f71]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_32,negated_conjecture,
% 2.32/0.93      ( v1_funct_1(sK2) ),
% 2.32/0.93      inference(cnf_transformation,[],[f72]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_564,plain,
% 2.32/0.93      ( ~ v1_relat_1(sK2) | k1_relat_1(sK2) = sK1 ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_562,c_33,c_32,c_30]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4065,plain,
% 2.32/0.93      ( k1_relat_1(sK2) = sK1 ),
% 2.32/0.93      inference(global_propositional_subsumption,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_3919,c_33,c_32,c_30,c_562,c_3931,c_3966]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4611,plain,
% 2.32/0.93      ( k1_relat_1(k5_relat_1(sK3,sK2)) = k10_relat_1(sK3,sK1) ),
% 2.32/0.93      inference(light_normalisation,[status(thm)],[c_4609,c_4065]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_26,negated_conjecture,
% 2.32/0.93      ( k1_relat_1(sK3) != k1_relat_1(k5_relat_1(sK3,sK2)) ),
% 2.32/0.93      inference(cnf_transformation,[],[f78]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_4650,plain,
% 2.32/0.93      ( k10_relat_1(sK3,sK1) != k1_relat_1(sK3) ),
% 2.32/0.93      inference(demodulation,[status(thm)],[c_4611,c_26]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3095,plain,
% 2.32/0.93      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.32/0.93      theory(equality) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3772,plain,
% 2.32/0.93      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_3095]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_3774,plain,
% 2.32/0.93      ( v1_xboole_0(sK1)
% 2.32/0.93      | ~ v1_xboole_0(k1_xboole_0)
% 2.32/0.93      | sK1 != k1_xboole_0 ),
% 2.32/0.93      inference(instantiation,[status(thm)],[c_3772]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(c_0,plain,
% 2.32/0.93      ( v1_xboole_0(k1_xboole_0) ),
% 2.32/0.93      inference(cnf_transformation,[],[f45]) ).
% 2.32/0.93  
% 2.32/0.93  cnf(contradiction,plain,
% 2.32/0.93      ( $false ),
% 2.32/0.93      inference(minisat,
% 2.32/0.93                [status(thm)],
% 2.32/0.93                [c_5439,c_5360,c_4650,c_3774,c_0,c_40,c_33]) ).
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/0.93  
% 2.32/0.93  ------                               Statistics
% 2.32/0.93  
% 2.32/0.93  ------ General
% 2.32/0.93  
% 2.32/0.93  abstr_ref_over_cycles:                  0
% 2.32/0.93  abstr_ref_under_cycles:                 0
% 2.32/0.93  gc_basic_clause_elim:                   0
% 2.32/0.93  forced_gc_time:                         0
% 2.32/0.93  parsing_time:                           0.01
% 2.32/0.93  unif_index_cands_time:                  0.
% 2.32/0.93  unif_index_add_time:                    0.
% 2.32/0.93  orderings_time:                         0.
% 2.32/0.93  out_proof_time:                         0.009
% 2.32/0.93  total_time:                             0.159
% 2.32/0.93  num_of_symbols:                         53
% 2.32/0.93  num_of_terms:                           3402
% 2.32/0.93  
% 2.32/0.93  ------ Preprocessing
% 2.32/0.93  
% 2.32/0.93  num_of_splits:                          0
% 2.32/0.93  num_of_split_atoms:                     0
% 2.32/0.93  num_of_reused_defs:                     0
% 2.32/0.93  num_eq_ax_congr_red:                    24
% 2.32/0.93  num_of_sem_filtered_clauses:            1
% 2.32/0.93  num_of_subtypes:                        0
% 2.32/0.93  monotx_restored_types:                  0
% 2.32/0.93  sat_num_of_epr_types:                   0
% 2.32/0.93  sat_num_of_non_cyclic_types:            0
% 2.32/0.93  sat_guarded_non_collapsed_types:        0
% 2.32/0.93  num_pure_diseq_elim:                    0
% 2.32/0.93  simp_replaced_by:                       0
% 2.32/0.93  res_preprocessed:                       137
% 2.32/0.93  prep_upred:                             0
% 2.32/0.93  prep_unflattend:                        148
% 2.32/0.93  smt_new_axioms:                         0
% 2.32/0.93  pred_elim_cands:                        6
% 2.32/0.93  pred_elim:                              3
% 2.32/0.93  pred_elim_cl:                           4
% 2.32/0.93  pred_elim_cycles:                       10
% 2.32/0.93  merged_defs:                            0
% 2.32/0.93  merged_defs_ncl:                        0
% 2.32/0.93  bin_hyper_res:                          0
% 2.32/0.93  prep_cycles:                            4
% 2.32/0.93  pred_elim_time:                         0.053
% 2.32/0.93  splitting_time:                         0.
% 2.32/0.93  sem_filter_time:                        0.
% 2.32/0.93  monotx_time:                            0.001
% 2.32/0.93  subtype_inf_time:                       0.
% 2.32/0.93  
% 2.32/0.93  ------ Problem properties
% 2.32/0.93  
% 2.32/0.93  clauses:                                25
% 2.32/0.93  conjectures:                            7
% 2.32/0.93  epr:                                    7
% 2.32/0.93  horn:                                   20
% 2.32/0.93  ground:                                 8
% 2.32/0.93  unary:                                  9
% 2.32/0.93  binary:                                 3
% 2.32/0.93  lits:                                   68
% 2.32/0.93  lits_eq:                                11
% 2.32/0.93  fd_pure:                                0
% 2.32/0.93  fd_pseudo:                              0
% 2.32/0.93  fd_cond:                                2
% 2.32/0.93  fd_pseudo_cond:                         1
% 2.32/0.93  ac_symbols:                             0
% 2.32/0.93  
% 2.32/0.93  ------ Propositional Solver
% 2.32/0.93  
% 2.32/0.93  prop_solver_calls:                      27
% 2.32/0.93  prop_fast_solver_calls:                 1563
% 2.32/0.93  smt_solver_calls:                       0
% 2.32/0.93  smt_fast_solver_calls:                  0
% 2.32/0.93  prop_num_of_clauses:                    1128
% 2.32/0.93  prop_preprocess_simplified:             5372
% 2.32/0.93  prop_fo_subsumed:                       85
% 2.32/0.93  prop_solver_time:                       0.
% 2.32/0.93  smt_solver_time:                        0.
% 2.32/0.93  smt_fast_solver_time:                   0.
% 2.32/0.93  prop_fast_solver_time:                  0.
% 2.32/0.93  prop_unsat_core_time:                   0.
% 2.32/0.93  
% 2.32/0.93  ------ QBF
% 2.32/0.93  
% 2.32/0.93  qbf_q_res:                              0
% 2.32/0.93  qbf_num_tautologies:                    0
% 2.32/0.93  qbf_prep_cycles:                        0
% 2.32/0.93  
% 2.32/0.93  ------ BMC1
% 2.32/0.93  
% 2.32/0.93  bmc1_current_bound:                     -1
% 2.32/0.93  bmc1_last_solved_bound:                 -1
% 2.32/0.93  bmc1_unsat_core_size:                   -1
% 2.32/0.93  bmc1_unsat_core_parents_size:           -1
% 2.32/0.93  bmc1_merge_next_fun:                    0
% 2.32/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.32/0.93  
% 2.32/0.93  ------ Instantiation
% 2.32/0.93  
% 2.32/0.93  inst_num_of_clauses:                    292
% 2.32/0.93  inst_num_in_passive:                    27
% 2.32/0.93  inst_num_in_active:                     222
% 2.32/0.93  inst_num_in_unprocessed:                43
% 2.32/0.93  inst_num_of_loops:                      230
% 2.32/0.93  inst_num_of_learning_restarts:          0
% 2.32/0.93  inst_num_moves_active_passive:          5
% 2.32/0.93  inst_lit_activity:                      0
% 2.32/0.93  inst_lit_activity_moves:                0
% 2.32/0.93  inst_num_tautologies:                   0
% 2.32/0.93  inst_num_prop_implied:                  0
% 2.32/0.93  inst_num_existing_simplified:           0
% 2.32/0.93  inst_num_eq_res_simplified:             0
% 2.32/0.93  inst_num_child_elim:                    0
% 2.32/0.93  inst_num_of_dismatching_blockings:      57
% 2.32/0.93  inst_num_of_non_proper_insts:           275
% 2.32/0.93  inst_num_of_duplicates:                 0
% 2.32/0.93  inst_inst_num_from_inst_to_res:         0
% 2.32/0.93  inst_dismatching_checking_time:         0.
% 2.32/0.93  
% 2.32/0.93  ------ Resolution
% 2.32/0.93  
% 2.32/0.93  res_num_of_clauses:                     0
% 2.32/0.93  res_num_in_passive:                     0
% 2.32/0.93  res_num_in_active:                      0
% 2.32/0.93  res_num_of_loops:                       141
% 2.32/0.93  res_forward_subset_subsumed:            37
% 2.32/0.93  res_backward_subset_subsumed:           0
% 2.32/0.93  res_forward_subsumed:                   0
% 2.32/0.93  res_backward_subsumed:                  0
% 2.32/0.93  res_forward_subsumption_resolution:     0
% 2.32/0.93  res_backward_subsumption_resolution:    0
% 2.32/0.93  res_clause_to_clause_subsumption:       87
% 2.32/0.93  res_orphan_elimination:                 0
% 2.32/0.93  res_tautology_del:                      38
% 2.32/0.93  res_num_eq_res_simplified:              0
% 2.32/0.93  res_num_sel_changes:                    0
% 2.32/0.93  res_moves_from_active_to_pass:          0
% 2.32/0.93  
% 2.32/0.93  ------ Superposition
% 2.32/0.93  
% 2.32/0.93  sup_time_total:                         0.
% 2.32/0.93  sup_time_generating:                    0.
% 2.32/0.93  sup_time_sim_full:                      0.
% 2.32/0.93  sup_time_sim_immed:                     0.
% 2.32/0.93  
% 2.32/0.93  sup_num_of_clauses:                     61
% 2.32/0.93  sup_num_in_active:                      44
% 2.32/0.93  sup_num_in_passive:                     17
% 2.32/0.93  sup_num_of_loops:                       44
% 2.32/0.93  sup_fw_superposition:                   32
% 2.32/0.93  sup_bw_superposition:                   17
% 2.32/0.93  sup_immediate_simplified:               23
% 2.32/0.93  sup_given_eliminated:                   0
% 2.32/0.93  comparisons_done:                       0
% 2.32/0.93  comparisons_avoided:                    1
% 2.32/0.93  
% 2.32/0.93  ------ Simplifications
% 2.32/0.93  
% 2.32/0.93  
% 2.32/0.93  sim_fw_subset_subsumed:                 4
% 2.32/0.93  sim_bw_subset_subsumed:                 0
% 2.32/0.93  sim_fw_subsumed:                        2
% 2.32/0.93  sim_bw_subsumed:                        0
% 2.32/0.93  sim_fw_subsumption_res:                 0
% 2.32/0.93  sim_bw_subsumption_res:                 0
% 2.32/0.93  sim_tautology_del:                      0
% 2.32/0.93  sim_eq_tautology_del:                   1
% 2.32/0.93  sim_eq_res_simp:                        0
% 2.32/0.93  sim_fw_demodulated:                     2
% 2.32/0.93  sim_bw_demodulated:                     1
% 2.32/0.93  sim_light_normalised:                   17
% 2.32/0.93  sim_joinable_taut:                      0
% 2.32/0.93  sim_joinable_simp:                      0
% 2.32/0.93  sim_ac_normalised:                      0
% 2.32/0.93  sim_smt_subsumption:                    0
% 2.32/0.93  
%------------------------------------------------------------------------------
