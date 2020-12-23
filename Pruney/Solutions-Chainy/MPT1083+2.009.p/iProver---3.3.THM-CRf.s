%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:29 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 594 expanded)
%              Number of clauses        :   81 ( 175 expanded)
%              Number of leaves         :   17 ( 165 expanded)
%              Depth                    :   16
%              Number of atoms          :  445 (3403 expanded)
%              Number of equality atoms :  155 ( 605 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1))
        & v1_funct_1(sK2)
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK1,X0,X0)
        & v1_funct_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f40,f39,f38])).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_812,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_830,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_819,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3090,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_819])).

cnf(c_7264,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_3090])).

cnf(c_7578,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_7264])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_823,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8518,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7578,c_823])).

cnf(c_8555,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_812,c_8518])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_825,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1396,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_812,c_825])).

cnf(c_8663,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_8555,c_1396])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_821,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8823,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8663,c_821])).

cnf(c_8849,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8823])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_811,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_817,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2871,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_partfun1(sK1,sK0) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_817])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1200,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1201,plain,
    ( v1_funct_2(sK1,X0,X1) != iProver_top
    | v1_partfun1(sK1,X0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_1203,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_partfun1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_3635,plain,
    ( v1_partfun1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2871,c_27,c_28,c_29,c_30,c_1203])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_815,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3640,plain,
    ( k1_relat_1(sK1) = sK0
    | v4_relat_1(sK1,sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3635,c_815])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_69,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1096,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1202,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1249,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4154,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_26,c_25,c_24,c_23,c_69,c_1032,c_1096,c_1202,c_1249])).

cnf(c_829,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1883,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_829])).

cnf(c_68,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_70,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_1033,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_2285,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1883,c_30,c_70,c_1033])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_824,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3059,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_824])).

cnf(c_3519,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_2285,c_3059])).

cnf(c_4158,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_4154,c_3519])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_822,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4522,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_822])).

cnf(c_31,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5531,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4522,c_30,c_31,c_70,c_1033])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_831,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5536,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_831])).

cnf(c_19,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4521,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4158,c_19])).

cnf(c_1378,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1383,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1056,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1057,plain,
    ( v5_relat_1(sK2,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( v5_relat_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8849,c_5536,c_4521,c_1383,c_1057,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 25
% 3.86/0.99  conjectures                             8
% 3.86/0.99  EPR                                     8
% 3.86/0.99  Horn                                    24
% 3.86/0.99  unary                                   10
% 3.86/0.99  binary                                  3
% 3.86/0.99  lits                                    58
% 3.86/0.99  lits eq                                 6
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 0
% 3.86/0.99  fd_pseudo_cond                          2
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Input Options Time Limit: Unbounded
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f14,conjecture,(
% 3.86/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f15,negated_conjecture,(
% 3.86/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 3.86/0.99    inference(negated_conjecture,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f15])).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 3.86/0.99    inference(flattening,[],[f32])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ( ! [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1)) & v1_funct_1(sK2) & v5_relat_1(sK2,X0) & v1_relat_1(sK2))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK1,X0,X0) & v1_funct_1(sK1))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ((k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f40,f39,f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f65,plain,(
% 3.86/0.99    v1_relat_1(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f70,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f11,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.86/0.99    inference(ennf_transformation,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.86/0.99    inference(flattening,[],[f26])).
% 3.86/0.99  
% 3.86/0.99  fof(f56,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f10,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f10])).
% 3.86/0.99  
% 3.86/0.99  fof(f54,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f25])).
% 3.86/0.99  
% 3.86/0.99  fof(f7,axiom,(
% 3.86/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f20,plain,(
% 3.86/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.86/0.99    inference(ennf_transformation,[],[f7])).
% 3.86/0.99  
% 3.86/0.99  fof(f21,plain,(
% 3.86/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(flattening,[],[f20])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f18,plain,(
% 3.86/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f49,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f9,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f23,plain,(
% 3.86/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.86/0.99    inference(ennf_transformation,[],[f9])).
% 3.86/0.99  
% 3.86/0.99  fof(f24,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.86/0.99    inference(flattening,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f24])).
% 3.86/0.99  
% 3.86/0.99  fof(f64,plain,(
% 3.86/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f12,axiom,(
% 3.86/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.86/0.99    inference(flattening,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f58,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f29])).
% 3.86/0.99  
% 3.86/0.99  fof(f61,plain,(
% 3.86/0.99    ~v1_xboole_0(sK0)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f62,plain,(
% 3.86/0.99    v1_funct_1(sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f63,plain,(
% 3.86/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,axiom,(
% 3.86/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.86/0.99    inference(ennf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(flattening,[],[f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f59,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f37])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f48,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f16,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f45,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f6,axiom,(
% 3.86/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f19,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f6])).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f19])).
% 3.86/0.99  
% 3.86/0.99  fof(f8,axiom,(
% 3.86/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f22,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f8])).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f22])).
% 3.86/0.99  
% 3.86/0.99  fof(f44,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f68,plain,(
% 3.86/0.99    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f17,plain,(
% 3.86/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f17])).
% 3.86/0.99  
% 3.86/0.99  fof(f46,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f36])).
% 3.86/0.99  
% 3.86/0.99  fof(f67,plain,(
% 3.86/0.99    v1_funct_1(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    v5_relat_1(sK2,sK0)),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_22,negated_conjecture,
% 3.86/0.99      ( v1_relat_1(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_812,plain,
% 3.86/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_830,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_14,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.86/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.86/0.99      | ~ v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_818,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13,plain,
% 3.86/0.99      ( v4_relat_1(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_819,plain,
% 3.86/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3090,plain,
% 3.86/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_818,c_819]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7264,plain,
% 3.86/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_830,c_3090]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7578,plain,
% 3.86/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_830,c_7264]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9,plain,
% 3.86/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_823,plain,
% 3.86/0.99      ( k7_relat_1(X0,X1) = X0
% 3.86/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8518,plain,
% 3.86/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7578,c_823]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8555,plain,
% 3.86/0.99      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_812,c_8518]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7,plain,
% 3.86/0.99      ( ~ v1_relat_1(X0)
% 3.86/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_825,plain,
% 3.86/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1396,plain,
% 3.86/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_812,c_825]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8663,plain,
% 3.86/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_8555,c_1396]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11,plain,
% 3.86/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.86/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.86/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.86/0.99      | ~ v1_funct_1(X1)
% 3.86/0.99      | ~ v1_relat_1(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_821,plain,
% 3.86/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 3.86/0.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.86/0.99      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8823,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK2) != iProver_top
% 3.86/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_8663,c_821]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8849,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK2) != iProver_top
% 3.86/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_8823]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_23,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_811,plain,
% 3.86/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/0.99      | v1_partfun1(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | v1_xboole_0(X2)
% 3.86/0.99      | ~ v1_funct_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_817,plain,
% 3.86/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.86/0.99      | v1_partfun1(X0,X1) = iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | v1_xboole_0(X2) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2871,plain,
% 3.86/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/0.99      | v1_partfun1(sK1,sK0) = iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.86/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_811,c_817]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_26,negated_conjecture,
% 3.86/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_27,plain,
% 3.86/0.99      ( v1_xboole_0(sK0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_25,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_28,plain,
% 3.86/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_24,negated_conjecture,
% 3.86/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_29,plain,
% 3.86/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_30,plain,
% 3.86/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1200,plain,
% 3.86/0.99      ( ~ v1_funct_2(sK1,X0,X1)
% 3.86/0.99      | v1_partfun1(sK1,X0)
% 3.86/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | v1_xboole_0(X1)
% 3.86/0.99      | ~ v1_funct_1(sK1) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1201,plain,
% 3.86/0.99      ( v1_funct_2(sK1,X0,X1) != iProver_top
% 3.86/0.99      | v1_partfun1(sK1,X0) = iProver_top
% 3.86/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/0.99      | v1_xboole_0(X1) = iProver_top
% 3.86/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1203,plain,
% 3.86/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/0.99      | v1_partfun1(sK1,sK0) = iProver_top
% 3.86/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.86/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1201]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3635,plain,
% 3.86/0.99      ( v1_partfun1(sK1,sK0) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_2871,c_27,c_28,c_29,c_30,c_1203]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_18,plain,
% 3.86/0.99      ( ~ v1_partfun1(X0,X1)
% 3.86/0.99      | ~ v4_relat_1(X0,X1)
% 3.86/0.99      | ~ v1_relat_1(X0)
% 3.86/0.99      | k1_relat_1(X0) = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_815,plain,
% 3.86/0.99      ( k1_relat_1(X0) = X1
% 3.86/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.86/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3640,plain,
% 3.86/0.99      ( k1_relat_1(sK1) = sK0
% 3.86/0.99      | v4_relat_1(sK1,sK0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3635,c_815]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6,plain,
% 3.86/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_69,plain,
% 3.86/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1032,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.86/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.86/0.99      | v1_relat_1(sK1) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1096,plain,
% 3.86/0.99      ( v4_relat_1(sK1,sK0)
% 3.86/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1202,plain,
% 3.86/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.86/0.99      | v1_partfun1(sK1,sK0)
% 3.86/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.86/0.99      | v1_xboole_0(sK0)
% 3.86/0.99      | ~ v1_funct_1(sK1) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1200]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1249,plain,
% 3.86/0.99      ( ~ v1_partfun1(sK1,sK0)
% 3.86/0.99      | ~ v4_relat_1(sK1,sK0)
% 3.86/0.99      | ~ v1_relat_1(sK1)
% 3.86/0.99      | k1_relat_1(sK1) = sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4154,plain,
% 3.86/0.99      ( k1_relat_1(sK1) = sK0 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3640,c_26,c_25,c_24,c_23,c_69,c_1032,c_1096,c_1202,
% 3.86/0.99                 c_1249]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_829,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1883,plain,
% 3.86/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_811,c_829]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_68,plain,
% 3.86/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_70,plain,
% 3.86/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1033,plain,
% 3.86/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.86/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2285,plain,
% 3.86/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_1883,c_30,c_70,c_1033]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8,plain,
% 3.86/0.99      ( ~ v1_relat_1(X0)
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_824,plain,
% 3.86/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3059,plain,
% 3.86/0.99      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_812,c_824]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3519,plain,
% 3.86/0.99      ( k10_relat_1(sK2,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2285,c_3059]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4158,plain,
% 3.86/0.99      ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_4154,c_3519]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.86/0.99      | ~ v1_relat_1(X0)
% 3.86/0.99      | ~ v1_relat_1(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_822,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4522,plain,
% 3.86/0.99      ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top
% 3.86/0.99      | v1_relat_1(sK1) != iProver_top
% 3.86/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_4158,c_822]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_31,plain,
% 3.86/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5531,plain,
% 3.86/0.99      ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_4522,c_30,c_31,c_70,c_1033]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_0,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_831,plain,
% 3.86/0.99      ( X0 = X1
% 3.86/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.86/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5536,plain,
% 3.86/0.99      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5531,c_831]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,negated_conjecture,
% 3.86/0.99      ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4521,plain,
% 3.86/0.99      ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2) ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_4158,c_19]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1378,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1383,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5,plain,
% 3.86/0.99      ( ~ v5_relat_1(X0,X1)
% 3.86/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.86/0.99      | ~ v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1056,plain,
% 3.86/0.99      ( ~ v5_relat_1(sK2,sK0)
% 3.86/0.99      | r1_tarski(k2_relat_1(sK2),sK0)
% 3.86/0.99      | ~ v1_relat_1(sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1057,plain,
% 3.86/0.99      ( v5_relat_1(sK2,sK0) != iProver_top
% 3.86/0.99      | r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
% 3.86/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_20,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_33,plain,
% 3.86/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,negated_conjecture,
% 3.86/0.99      ( v5_relat_1(sK2,sK0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_32,plain,
% 3.86/0.99      ( v5_relat_1(sK2,sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(contradiction,plain,
% 3.86/0.99      ( $false ),
% 3.86/0.99      inference(minisat,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_8849,c_5536,c_4521,c_1383,c_1057,c_33,c_32,c_31]) ).
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  ------                               Statistics
% 3.86/0.99  
% 3.86/0.99  ------ Selected
% 3.86/0.99  
% 3.86/0.99  total_time:                             0.27
% 3.86/0.99  
%------------------------------------------------------------------------------
