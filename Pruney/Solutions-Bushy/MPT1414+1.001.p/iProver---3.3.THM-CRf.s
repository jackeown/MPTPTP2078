%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:40 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  261 (1621 expanded)
%              Number of clauses        :  173 ( 376 expanded)
%              Number of leaves         :   22 ( 579 expanded)
%              Depth                    :   22
%              Number of atoms          : 1275 (12474 expanded)
%              Number of equality atoms :  176 ( 283 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f50])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r3_binop_1(X0,X2,X3)
                   => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r3_binop_1(X0,X2,X3)
                     => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK4))
        & r3_binop_1(X0,X2,sK4)
        & m2_filter_1(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
              & r3_binop_1(X0,X2,X3)
              & m2_filter_1(X3,X0,X1) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK3),k3_filter_1(X0,X1,X3))
            & r3_binop_1(X0,sK3,X3)
            & m2_filter_1(X3,X0,X1) )
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_binop_1(k8_eqrel_1(X0,sK2),k9_eqrel_1(X0,sK2,X2),k3_filter_1(X0,sK2,X3))
                & r3_binop_1(X0,X2,X3)
                & m2_filter_1(X3,X0,sK2) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK2)
        & v3_relat_2(sK2)
        & v1_partfun1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r3_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(sK1,X1),k9_eqrel_1(sK1,X1,X2),k3_filter_1(sK1,X1,X3))
                  & r3_binop_1(sK1,X2,X3)
                  & m2_filter_1(X3,sK1,X1) )
              & m1_subset_1(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    & r3_binop_1(sK1,sK3,sK4)
    & m2_filter_1(sK4,sK1,sK2)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v8_relat_2(sK2)
    & v3_relat_2(sK2)
    & v1_partfun1(sK2,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f47,f56,f55,f54,f53])).

fof(f82,plain,(
    v1_partfun1(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    v8_relat_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v3_relat_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f48])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    m2_filter_1(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    r3_binop_1(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r2_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r1_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1751,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_30,negated_conjecture,
    ( v1_partfun1(sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( v8_relat_2(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_842,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_843,plain,
    ( ~ v1_partfun1(sK2,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_29,negated_conjecture,
    ( v3_relat_2(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_847,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k7_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ v1_partfun1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_29])).

cnf(c_848,plain,
    ( ~ v1_partfun1(sK2,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(renaming,[status(thm)],[c_847])).

cnf(c_1013,plain,
    ( m1_subset_1(k7_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | sK2 != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_848])).

cnf(c_1014,plain,
    ( m1_subset_1(k7_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_845,plain,
    ( ~ v1_partfun1(sK2,sK1)
    | m1_subset_1(k7_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1016,plain,
    ( m1_subset_1(k7_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_30,c_29,c_27,c_845])).

cnf(c_1738,plain,
    ( m1_subset_1(k7_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_821,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_822,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2)
    | k7_eqrel_1(X0,sK2) = k8_eqrel_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK2,X0)
    | k7_eqrel_1(X0,sK2) = k8_eqrel_1(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_29])).

cnf(c_827,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK2) = k8_eqrel_1(X0,sK2) ),
    inference(renaming,[status(thm)],[c_826])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK2) = k8_eqrel_1(X0,sK2)
    | sK2 != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_827])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k7_eqrel_1(sK1,sK2) = k8_eqrel_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_824,plain,
    ( ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2)
    | k7_eqrel_1(sK1,sK2) = k8_eqrel_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1027,plain,
    ( k7_eqrel_1(sK1,sK2) = k8_eqrel_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_30,c_29,c_27,c_824])).

cnf(c_1772,plain,
    ( m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1738,c_1027])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_19,c_20])).

cnf(c_1747,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_2229,plain,
    ( m1_subset_1(X0,k8_eqrel_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1747])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v1_partfun1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( v3_relat_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( ~ m1_eqrel_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_eqrel_1(k8_eqrel_1(X1,X0),X1)
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_374,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | X1 != X3
    | k8_eqrel_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_375,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_770,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_375,c_28])).

cnf(c_771,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k8_eqrel_1(X0,sK2)) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_772,plain,
    ( v1_partfun1(sK2,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v3_relat_2(sK2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k8_eqrel_1(X0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_774,plain,
    ( v1_partfun1(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v3_relat_2(sK2) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_10,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_472,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | k9_eqrel_1(X1,X0,X2) != X3
    | k8_eqrel_1(X1,X0) != X4
    | k1_zfmisc_1(X1) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_473,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( v1_xboole_0(X1)
    | ~ v8_relat_2(X0)
    | ~ v3_relat_2(X0)
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_375])).

cnf(c_478,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_737,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_478,c_28])).

cnf(c_738,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_742,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK2,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_29])).

cnf(c_743,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_eqrel_1(X1,sK2,X0),k8_eqrel_1(X1,sK2))
    | ~ m1_subset_1(k8_eqrel_1(X1,sK2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_743])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_31,c_27])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1067])).

cnf(c_1734,plain,
    ( m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_1784,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1734,c_1772])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1750,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,X0,X2) = k11_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_794,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,X0,X2) = k11_relat_1(X0,X2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_795,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2)
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK2,X1) = k11_relat_1(sK2,X1) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_799,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK2,X0)
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK2,X1) = k11_relat_1(sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_29])).

cnf(c_800,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK2,X1) = k11_relat_1(sK2,X1) ),
    inference(renaming,[status(thm)],[c_799])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,sK2,X0) = k11_relat_1(sK2,X0)
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_800])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_xboole_0(sK1)
    | k9_eqrel_1(sK1,sK2,X0) = k11_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1032])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k9_eqrel_1(sK1,sK2,X0) = k11_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_31,c_27])).

cnf(c_1737,plain,
    ( k9_eqrel_1(sK1,sK2,X0) = k11_relat_1(sK2,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_2311,plain,
    ( k9_eqrel_1(sK1,sK2,sK3) = k11_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1750,c_1737])).

cnf(c_1322,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1067])).

cnf(c_1735,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_2354,plain,
    ( m1_subset_1(k11_relat_1(sK2,sK3),k8_eqrel_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_1735])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2664,plain,
    ( m1_subset_1(k11_relat_1(sK2,sK3),k8_eqrel_1(sK1,sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2354,c_37])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | k9_eqrel_1(sK1,sK2,sK3) != X2
    | k3_filter_1(sK1,sK2,sK4) != X0
    | k8_eqrel_1(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_670,plain,
    ( ~ v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ v1_funct_1(k3_filter_1(sK1,sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_1741,plain,
    ( v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)) != iProver_top
    | r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) != iProver_top
    | r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) != iProver_top
    | m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k3_filter_1(sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( m2_filter_1(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_591,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_592,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_594,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_31])).

cnf(c_595,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_594])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_595])).

cnf(c_623,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_624,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_626,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_12,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_577,plain,
    ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_578,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_580,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_31])).

cnf(c_581,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_580])).

cnf(c_635,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_581])).

cnf(c_636,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_637,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_639,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_13,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_563,plain,
    ( v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X2)
    | sK4 != X0
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_564,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_566,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_31])).

cnf(c_567,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_566])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_1(sK4)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_567])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_650,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_671,plain,
    ( v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)) != iProver_top
    | r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) != iProver_top
    | r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) != iProver_top
    | m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k3_filter_1(sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( r3_binop_1(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_691,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_692,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_693,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(sK1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_702,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_703,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_704,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r2_binop_1(sK1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_22,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r2_binop_1(X1,X3,X0)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_521,plain,
    ( ~ r2_binop_1(X0,X1,X2)
    | r2_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
    | ~ v1_partfun1(X3,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | v1_xboole_0(X0)
    | sK4 != X2
    | sK2 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_522,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,X0,sK4)
    | ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2)
    | ~ v8_relat_2(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_526,plain,
    ( ~ r2_binop_1(sK1,X0,sK4)
    | r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_31,c_30,c_29,c_28,c_27])).

cnf(c_527,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,X0,sK4)
    | ~ m1_subset_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_526])).

cnf(c_1907,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_1908,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) = iProver_top
    | r2_binop_1(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_21,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r1_binop_1(X1,X3,X0)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_542,plain,
    ( ~ r1_binop_1(X0,X1,X2)
    | r1_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
    | ~ v1_partfun1(X3,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | v1_xboole_0(X0)
    | sK4 != X2
    | sK2 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_543,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,X0,sK4)
    | ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2)
    | ~ v8_relat_2(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( ~ r1_binop_1(sK1,X0,sK4)
    | r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_31,c_30,c_29,c_28,c_27])).

cnf(c_548,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,X0,sK4)
    | ~ m1_subset_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_1910,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_1911,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) = iProver_top
    | r1_binop_1(sK1,sK3,sK4) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1910])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_929,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_930,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_29])).

cnf(c_935,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1085,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_935])).

cnf(c_1086,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1085])).

cnf(c_1090,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_31,c_27])).

cnf(c_1091,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1090])).

cnf(c_1921,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1922,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_896,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_897,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_901,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_29])).

cnf(c_902,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_1109,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_902])).

cnf(c_1110,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_1114,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_31,c_27])).

cnf(c_1115,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1114])).

cnf(c_1920,plain,
    ( v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1924,plain,
    ( v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)) = iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_863,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_864,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_868,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_29])).

cnf(c_869,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_868])).

cnf(c_1133,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1)
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_869])).

cnf(c_1134,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK1,sK2,X0))
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1133])).

cnf(c_1138,plain,
    ( v1_funct_1(k3_filter_1(sK1,sK2,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1134,c_31,c_27])).

cnf(c_1139,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK1,sK2,X0)) ),
    inference(renaming,[status(thm)],[c_1138])).

cnf(c_1919,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | v1_funct_1(k3_filter_1(sK1,sK2,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1926,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(k3_filter_1(sK1,sK2,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_2742,plain,
    ( m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_36,c_37,c_626,c_639,c_652,c_671,c_693,c_704,c_1908,c_1911,c_1922,c_1924,c_1926])).

cnf(c_2746,plain,
    ( m1_subset_1(k11_relat_1(sK2,sK3),k8_eqrel_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2742,c_2311])).

cnf(c_2906,plain,
    ( m1_subset_1(X0,k8_eqrel_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2229,c_32,c_33,c_34,c_36,c_37,c_774,c_1784,c_2354,c_2746])).

cnf(c_2913,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1751,c_2906])).


%------------------------------------------------------------------------------
