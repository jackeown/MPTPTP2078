%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:56 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 998 expanded)
%              Number of clauses        :  134 ( 221 expanded)
%              Number of leaves         :   18 ( 359 expanded)
%              Depth                    :   20
%              Number of atoms          : 1109 (7794 expanded)
%              Number of equality atoms :   66 (  85 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r3_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
              & r3_binop_1(X0,X2,X3)
              & m2_filter_1(X3,X0,X1) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK2),k3_filter_1(X0,X1,X3))
            & r3_binop_1(X0,sK2,X3)
            & m2_filter_1(X3,X0,X1) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
                ( ~ r3_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3))
                & r3_binop_1(X0,X2,X3)
                & m2_filter_1(X3,X0,sK1) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK1)
        & v3_relat_2(sK1)
        & v1_partfun1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
                  ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r3_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f47,f46,f45,f44])).

fof(f70,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f22])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f20])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_416,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,X0,X2) != X3
    | k8_eqrel_1(X1,X0) != X4
    | k1_zfmisc_1(X1) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_417,plain,
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
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_10,plain,
    ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,plain,
    ( ~ m1_eqrel_1(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_322,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | X3 != X1
    | k8_eqrel_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_323,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_421,plain,
    ( m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_323])).

cnf(c_422,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_25,negated_conjecture,
    ( v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_681,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_25])).

cnf(c_682,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_26,negated_conjecture,
    ( v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_686,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_26])).

cnf(c_687,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(renaming,[status(thm)],[c_686])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,sK1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_687])).

cnf(c_955,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_959,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_28,c_24])).

cnf(c_960,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(renaming,[status(thm)],[c_959])).

cnf(c_1198,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_960])).

cnf(c_1911,plain,
    ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK2,sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_780,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_781,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_26])).

cnf(c_786,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_1026,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_786])).

cnf(c_1027,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_1031,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1027,c_28,c_24])).

cnf(c_1032,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
    inference(renaming,[status(thm)],[c_1031])).

cnf(c_1743,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_813,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_814,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_818,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_26])).

cnf(c_819,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_818])).

cnf(c_1002,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_819])).

cnf(c_1003,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_1007,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_28,c_24])).

cnf(c_1008,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1007])).

cnf(c_1744,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_846,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_847,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_26])).

cnf(c_852,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_978,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_852])).

cnf(c_979,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_983,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_979,c_28,c_24])).

cnf(c_984,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_983])).

cnf(c_1745,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_18,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r1_binop_1(X1,X3,X0)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_486,plain,
    ( ~ r1_binop_1(X0,X1,X2)
    | r1_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
    | ~ v1_partfun1(X3,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | v1_xboole_0(X0)
    | sK3 != X2
    | sK1 != X3
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_487,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ r1_binop_1(sK0,X0,sK3)
    | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_28,c_27,c_26,c_25,c_24])).

cnf(c_492,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_1740,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_19,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r2_binop_1(X1,X3,X0)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_465,plain,
    ( ~ r2_binop_1(X0,X1,X2)
    | r2_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
    | ~ v1_partfun1(X3,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | v1_xboole_0(X0)
    | sK3 != X2
    | sK1 != X3
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_466,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_470,plain,
    ( ~ r2_binop_1(sK0,X0,sK3)
    | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_28,c_27,c_26,c_25,c_24])).

cnf(c_471,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_470])).

cnf(c_1737,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_756,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_757,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_26])).

cnf(c_762,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_762])).

cnf(c_925,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_759,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_927,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_925,c_28,c_27,c_26,c_24,c_759])).

cnf(c_1581,plain,
    ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_735,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_736,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_26])).

cnf(c_741,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_935,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_741])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_738,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_938,plain,
    ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_27,c_26,c_24,c_738])).

cnf(c_1606,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1581,c_938])).

cnf(c_1697,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1606])).

cnf(c_1199,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_960])).

cnf(c_714,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_323,c_25])).

cnf(c_715,plain,
    ( ~ v1_partfun1(sK1,X0)
    | m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_717,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_646,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_647,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_635,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_636,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_613,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | k9_eqrel_1(sK0,sK1,sK2) != X2
    | k3_filter_1(sK0,sK1,sK3) != X0
    | k8_eqrel_1(sK0,sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_614,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_507,plain,
    ( v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_508,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_510,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_28])).

cnf(c_511,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_1(sK3)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_511])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_14,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_521,plain,
    ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_522,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_524,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_28])).

cnf(c_525,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_579,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_525])).

cnf(c_580,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_13,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_535,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_536,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_538,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_28])).

cnf(c_539,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_539])).

cnf(c_567,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_569,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1911,c_1863,c_1743,c_1744,c_1745,c_1740,c_1737,c_1697,c_1199,c_717,c_647,c_636,c_614,c_595,c_582,c_569,c_23,c_24,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.83/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.00  
% 1.83/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.83/1.00  
% 1.83/1.00  ------  iProver source info
% 1.83/1.00  
% 1.83/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.83/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.83/1.00  git: non_committed_changes: false
% 1.83/1.00  git: last_make_outside_of_git: false
% 1.83/1.00  
% 1.83/1.00  ------ 
% 1.83/1.00  
% 1.83/1.00  ------ Input Options
% 1.83/1.00  
% 1.83/1.00  --out_options                           all
% 1.83/1.00  --tptp_safe_out                         true
% 1.83/1.00  --problem_path                          ""
% 1.83/1.00  --include_path                          ""
% 1.83/1.00  --clausifier                            res/vclausify_rel
% 1.83/1.00  --clausifier_options                    --mode clausify
% 1.83/1.00  --stdin                                 false
% 1.83/1.00  --stats_out                             all
% 1.83/1.00  
% 1.83/1.00  ------ General Options
% 1.83/1.00  
% 1.83/1.00  --fof                                   false
% 1.83/1.00  --time_out_real                         305.
% 1.83/1.00  --time_out_virtual                      -1.
% 1.83/1.00  --symbol_type_check                     false
% 1.83/1.00  --clausify_out                          false
% 1.83/1.00  --sig_cnt_out                           false
% 1.83/1.00  --trig_cnt_out                          false
% 1.83/1.00  --trig_cnt_out_tolerance                1.
% 1.83/1.00  --trig_cnt_out_sk_spl                   false
% 1.83/1.00  --abstr_cl_out                          false
% 1.83/1.00  
% 1.83/1.00  ------ Global Options
% 1.83/1.00  
% 1.83/1.00  --schedule                              default
% 1.83/1.00  --add_important_lit                     false
% 1.83/1.00  --prop_solver_per_cl                    1000
% 1.83/1.00  --min_unsat_core                        false
% 1.83/1.00  --soft_assumptions                      false
% 1.83/1.00  --soft_lemma_size                       3
% 1.83/1.00  --prop_impl_unit_size                   0
% 1.83/1.00  --prop_impl_unit                        []
% 1.83/1.00  --share_sel_clauses                     true
% 1.83/1.00  --reset_solvers                         false
% 1.83/1.00  --bc_imp_inh                            [conj_cone]
% 1.83/1.00  --conj_cone_tolerance                   3.
% 1.83/1.00  --extra_neg_conj                        none
% 1.83/1.00  --large_theory_mode                     true
% 1.83/1.00  --prolific_symb_bound                   200
% 1.83/1.00  --lt_threshold                          2000
% 1.83/1.00  --clause_weak_htbl                      true
% 1.83/1.00  --gc_record_bc_elim                     false
% 1.83/1.00  
% 1.83/1.00  ------ Preprocessing Options
% 1.83/1.00  
% 1.83/1.00  --preprocessing_flag                    true
% 1.83/1.00  --time_out_prep_mult                    0.1
% 1.83/1.00  --splitting_mode                        input
% 1.83/1.00  --splitting_grd                         true
% 1.83/1.00  --splitting_cvd                         false
% 1.83/1.00  --splitting_cvd_svl                     false
% 1.83/1.00  --splitting_nvd                         32
% 1.83/1.00  --sub_typing                            true
% 1.83/1.00  --prep_gs_sim                           true
% 1.83/1.00  --prep_unflatten                        true
% 1.83/1.00  --prep_res_sim                          true
% 1.83/1.00  --prep_upred                            true
% 1.83/1.00  --prep_sem_filter                       exhaustive
% 1.83/1.00  --prep_sem_filter_out                   false
% 1.83/1.00  --pred_elim                             true
% 1.83/1.00  --res_sim_input                         true
% 1.83/1.00  --eq_ax_congr_red                       true
% 1.83/1.00  --pure_diseq_elim                       true
% 1.83/1.00  --brand_transform                       false
% 1.83/1.00  --non_eq_to_eq                          false
% 1.83/1.00  --prep_def_merge                        true
% 1.83/1.00  --prep_def_merge_prop_impl              false
% 1.83/1.00  --prep_def_merge_mbd                    true
% 1.83/1.00  --prep_def_merge_tr_red                 false
% 1.83/1.00  --prep_def_merge_tr_cl                  false
% 1.83/1.00  --smt_preprocessing                     true
% 1.83/1.00  --smt_ac_axioms                         fast
% 1.83/1.00  --preprocessed_out                      false
% 1.83/1.00  --preprocessed_stats                    false
% 1.83/1.00  
% 1.83/1.00  ------ Abstraction refinement Options
% 1.83/1.00  
% 1.83/1.00  --abstr_ref                             []
% 1.83/1.00  --abstr_ref_prep                        false
% 1.83/1.00  --abstr_ref_until_sat                   false
% 1.83/1.00  --abstr_ref_sig_restrict                funpre
% 1.83/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.83/1.00  --abstr_ref_under                       []
% 1.83/1.00  
% 1.83/1.00  ------ SAT Options
% 1.83/1.00  
% 1.83/1.00  --sat_mode                              false
% 1.83/1.00  --sat_fm_restart_options                ""
% 1.83/1.00  --sat_gr_def                            false
% 1.83/1.00  --sat_epr_types                         true
% 1.83/1.00  --sat_non_cyclic_types                  false
% 1.83/1.00  --sat_finite_models                     false
% 1.83/1.00  --sat_fm_lemmas                         false
% 1.83/1.00  --sat_fm_prep                           false
% 1.83/1.00  --sat_fm_uc_incr                        true
% 1.83/1.00  --sat_out_model                         small
% 1.83/1.00  --sat_out_clauses                       false
% 1.83/1.00  
% 1.83/1.00  ------ QBF Options
% 1.83/1.00  
% 1.83/1.00  --qbf_mode                              false
% 1.83/1.00  --qbf_elim_univ                         false
% 1.83/1.00  --qbf_dom_inst                          none
% 1.83/1.00  --qbf_dom_pre_inst                      false
% 1.83/1.00  --qbf_sk_in                             false
% 1.83/1.00  --qbf_pred_elim                         true
% 1.83/1.00  --qbf_split                             512
% 1.83/1.00  
% 1.83/1.00  ------ BMC1 Options
% 1.83/1.00  
% 1.83/1.00  --bmc1_incremental                      false
% 1.83/1.00  --bmc1_axioms                           reachable_all
% 1.83/1.00  --bmc1_min_bound                        0
% 1.83/1.00  --bmc1_max_bound                        -1
% 1.83/1.00  --bmc1_max_bound_default                -1
% 1.83/1.00  --bmc1_symbol_reachability              true
% 1.83/1.00  --bmc1_property_lemmas                  false
% 1.83/1.00  --bmc1_k_induction                      false
% 1.83/1.00  --bmc1_non_equiv_states                 false
% 1.83/1.00  --bmc1_deadlock                         false
% 1.83/1.00  --bmc1_ucm                              false
% 1.83/1.00  --bmc1_add_unsat_core                   none
% 1.83/1.00  --bmc1_unsat_core_children              false
% 1.83/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.83/1.00  --bmc1_out_stat                         full
% 1.83/1.00  --bmc1_ground_init                      false
% 1.83/1.00  --bmc1_pre_inst_next_state              false
% 1.83/1.00  --bmc1_pre_inst_state                   false
% 1.83/1.00  --bmc1_pre_inst_reach_state             false
% 1.83/1.00  --bmc1_out_unsat_core                   false
% 1.83/1.00  --bmc1_aig_witness_out                  false
% 1.83/1.00  --bmc1_verbose                          false
% 1.83/1.00  --bmc1_dump_clauses_tptp                false
% 1.83/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.83/1.00  --bmc1_dump_file                        -
% 1.83/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.83/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.83/1.00  --bmc1_ucm_extend_mode                  1
% 1.83/1.00  --bmc1_ucm_init_mode                    2
% 1.83/1.00  --bmc1_ucm_cone_mode                    none
% 1.83/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.83/1.00  --bmc1_ucm_relax_model                  4
% 1.83/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.83/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.83/1.00  --bmc1_ucm_layered_model                none
% 1.83/1.00  --bmc1_ucm_max_lemma_size               10
% 1.83/1.00  
% 1.83/1.00  ------ AIG Options
% 1.83/1.00  
% 1.83/1.00  --aig_mode                              false
% 1.83/1.00  
% 1.83/1.00  ------ Instantiation Options
% 1.83/1.00  
% 1.83/1.00  --instantiation_flag                    true
% 1.83/1.00  --inst_sos_flag                         false
% 1.83/1.00  --inst_sos_phase                        true
% 1.83/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.83/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.83/1.00  --inst_lit_sel_side                     num_symb
% 1.83/1.00  --inst_solver_per_active                1400
% 1.83/1.00  --inst_solver_calls_frac                1.
% 1.83/1.00  --inst_passive_queue_type               priority_queues
% 1.83/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.83/1.00  --inst_passive_queues_freq              [25;2]
% 1.83/1.00  --inst_dismatching                      true
% 1.83/1.00  --inst_eager_unprocessed_to_passive     true
% 1.83/1.00  --inst_prop_sim_given                   true
% 1.83/1.00  --inst_prop_sim_new                     false
% 1.83/1.00  --inst_subs_new                         false
% 1.83/1.00  --inst_eq_res_simp                      false
% 1.83/1.00  --inst_subs_given                       false
% 1.83/1.00  --inst_orphan_elimination               true
% 1.83/1.00  --inst_learning_loop_flag               true
% 1.83/1.00  --inst_learning_start                   3000
% 1.83/1.00  --inst_learning_factor                  2
% 1.83/1.00  --inst_start_prop_sim_after_learn       3
% 1.83/1.00  --inst_sel_renew                        solver
% 1.83/1.00  --inst_lit_activity_flag                true
% 1.83/1.00  --inst_restr_to_given                   false
% 1.83/1.00  --inst_activity_threshold               500
% 1.83/1.00  --inst_out_proof                        true
% 1.83/1.00  
% 1.83/1.00  ------ Resolution Options
% 1.83/1.00  
% 1.83/1.00  --resolution_flag                       true
% 1.83/1.00  --res_lit_sel                           adaptive
% 1.83/1.00  --res_lit_sel_side                      none
% 1.83/1.00  --res_ordering                          kbo
% 1.83/1.00  --res_to_prop_solver                    active
% 1.83/1.00  --res_prop_simpl_new                    false
% 1.83/1.00  --res_prop_simpl_given                  true
% 1.83/1.00  --res_passive_queue_type                priority_queues
% 1.83/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.83/1.00  --res_passive_queues_freq               [15;5]
% 1.83/1.00  --res_forward_subs                      full
% 1.83/1.00  --res_backward_subs                     full
% 1.83/1.00  --res_forward_subs_resolution           true
% 1.83/1.00  --res_backward_subs_resolution          true
% 1.83/1.00  --res_orphan_elimination                true
% 1.83/1.00  --res_time_limit                        2.
% 1.83/1.00  --res_out_proof                         true
% 1.83/1.00  
% 1.83/1.00  ------ Superposition Options
% 1.83/1.00  
% 1.83/1.00  --superposition_flag                    true
% 1.83/1.00  --sup_passive_queue_type                priority_queues
% 1.83/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.83/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.83/1.00  --demod_completeness_check              fast
% 1.83/1.00  --demod_use_ground                      true
% 1.83/1.00  --sup_to_prop_solver                    passive
% 1.83/1.00  --sup_prop_simpl_new                    true
% 1.83/1.00  --sup_prop_simpl_given                  true
% 1.83/1.00  --sup_fun_splitting                     false
% 1.83/1.00  --sup_smt_interval                      50000
% 1.83/1.00  
% 1.83/1.00  ------ Superposition Simplification Setup
% 1.83/1.00  
% 1.83/1.00  --sup_indices_passive                   []
% 1.83/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.83/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_full_bw                           [BwDemod]
% 1.83/1.00  --sup_immed_triv                        [TrivRules]
% 1.83/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.83/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_immed_bw_main                     []
% 1.83/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.83/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.83/1.00  
% 1.83/1.00  ------ Combination Options
% 1.83/1.00  
% 1.83/1.00  --comb_res_mult                         3
% 1.83/1.00  --comb_sup_mult                         2
% 1.83/1.00  --comb_inst_mult                        10
% 1.83/1.00  
% 1.83/1.00  ------ Debug Options
% 1.83/1.00  
% 1.83/1.00  --dbg_backtrace                         false
% 1.83/1.00  --dbg_dump_prop_clauses                 false
% 1.83/1.00  --dbg_dump_prop_clauses_file            -
% 1.83/1.00  --dbg_out_stat                          false
% 1.83/1.00  ------ Parsing...
% 1.83/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.83/1.00  
% 1.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.83/1.00  
% 1.83/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.83/1.00  
% 1.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.83/1.00  ------ Proving...
% 1.83/1.00  ------ Problem Properties 
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  clauses                                 21
% 1.83/1.00  conjectures                             3
% 1.83/1.00  EPR                                     5
% 1.83/1.00  Horn                                    20
% 1.83/1.00  unary                                   11
% 1.83/1.00  binary                                  0
% 1.83/1.00  lits                                    47
% 1.83/1.00  lits eq                                 4
% 1.83/1.00  fd_pure                                 0
% 1.83/1.00  fd_pseudo                               0
% 1.83/1.00  fd_cond                                 0
% 1.83/1.00  fd_pseudo_cond                          0
% 1.83/1.00  AC symbols                              0
% 1.83/1.00  
% 1.83/1.00  ------ Schedule dynamic 5 is on 
% 1.83/1.00  
% 1.83/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  ------ 
% 1.83/1.00  Current options:
% 1.83/1.00  ------ 
% 1.83/1.00  
% 1.83/1.00  ------ Input Options
% 1.83/1.00  
% 1.83/1.00  --out_options                           all
% 1.83/1.00  --tptp_safe_out                         true
% 1.83/1.00  --problem_path                          ""
% 1.83/1.00  --include_path                          ""
% 1.83/1.00  --clausifier                            res/vclausify_rel
% 1.83/1.00  --clausifier_options                    --mode clausify
% 1.83/1.00  --stdin                                 false
% 1.83/1.00  --stats_out                             all
% 1.83/1.00  
% 1.83/1.00  ------ General Options
% 1.83/1.00  
% 1.83/1.00  --fof                                   false
% 1.83/1.00  --time_out_real                         305.
% 1.83/1.00  --time_out_virtual                      -1.
% 1.83/1.00  --symbol_type_check                     false
% 1.83/1.00  --clausify_out                          false
% 1.83/1.00  --sig_cnt_out                           false
% 1.83/1.00  --trig_cnt_out                          false
% 1.83/1.00  --trig_cnt_out_tolerance                1.
% 1.83/1.00  --trig_cnt_out_sk_spl                   false
% 1.83/1.00  --abstr_cl_out                          false
% 1.83/1.00  
% 1.83/1.00  ------ Global Options
% 1.83/1.00  
% 1.83/1.00  --schedule                              default
% 1.83/1.00  --add_important_lit                     false
% 1.83/1.00  --prop_solver_per_cl                    1000
% 1.83/1.00  --min_unsat_core                        false
% 1.83/1.00  --soft_assumptions                      false
% 1.83/1.00  --soft_lemma_size                       3
% 1.83/1.00  --prop_impl_unit_size                   0
% 1.83/1.00  --prop_impl_unit                        []
% 1.83/1.00  --share_sel_clauses                     true
% 1.83/1.00  --reset_solvers                         false
% 1.83/1.00  --bc_imp_inh                            [conj_cone]
% 1.83/1.00  --conj_cone_tolerance                   3.
% 1.83/1.00  --extra_neg_conj                        none
% 1.83/1.00  --large_theory_mode                     true
% 1.83/1.00  --prolific_symb_bound                   200
% 1.83/1.00  --lt_threshold                          2000
% 1.83/1.00  --clause_weak_htbl                      true
% 1.83/1.00  --gc_record_bc_elim                     false
% 1.83/1.00  
% 1.83/1.00  ------ Preprocessing Options
% 1.83/1.00  
% 1.83/1.00  --preprocessing_flag                    true
% 1.83/1.00  --time_out_prep_mult                    0.1
% 1.83/1.00  --splitting_mode                        input
% 1.83/1.00  --splitting_grd                         true
% 1.83/1.00  --splitting_cvd                         false
% 1.83/1.00  --splitting_cvd_svl                     false
% 1.83/1.00  --splitting_nvd                         32
% 1.83/1.00  --sub_typing                            true
% 1.83/1.00  --prep_gs_sim                           true
% 1.83/1.00  --prep_unflatten                        true
% 1.83/1.00  --prep_res_sim                          true
% 1.83/1.00  --prep_upred                            true
% 1.83/1.00  --prep_sem_filter                       exhaustive
% 1.83/1.00  --prep_sem_filter_out                   false
% 1.83/1.00  --pred_elim                             true
% 1.83/1.00  --res_sim_input                         true
% 1.83/1.00  --eq_ax_congr_red                       true
% 1.83/1.00  --pure_diseq_elim                       true
% 1.83/1.00  --brand_transform                       false
% 1.83/1.00  --non_eq_to_eq                          false
% 1.83/1.00  --prep_def_merge                        true
% 1.83/1.00  --prep_def_merge_prop_impl              false
% 1.83/1.00  --prep_def_merge_mbd                    true
% 1.83/1.00  --prep_def_merge_tr_red                 false
% 1.83/1.00  --prep_def_merge_tr_cl                  false
% 1.83/1.00  --smt_preprocessing                     true
% 1.83/1.00  --smt_ac_axioms                         fast
% 1.83/1.00  --preprocessed_out                      false
% 1.83/1.00  --preprocessed_stats                    false
% 1.83/1.00  
% 1.83/1.00  ------ Abstraction refinement Options
% 1.83/1.00  
% 1.83/1.00  --abstr_ref                             []
% 1.83/1.00  --abstr_ref_prep                        false
% 1.83/1.00  --abstr_ref_until_sat                   false
% 1.83/1.00  --abstr_ref_sig_restrict                funpre
% 1.83/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.83/1.00  --abstr_ref_under                       []
% 1.83/1.00  
% 1.83/1.00  ------ SAT Options
% 1.83/1.00  
% 1.83/1.00  --sat_mode                              false
% 1.83/1.00  --sat_fm_restart_options                ""
% 1.83/1.00  --sat_gr_def                            false
% 1.83/1.00  --sat_epr_types                         true
% 1.83/1.00  --sat_non_cyclic_types                  false
% 1.83/1.00  --sat_finite_models                     false
% 1.83/1.00  --sat_fm_lemmas                         false
% 1.83/1.00  --sat_fm_prep                           false
% 1.83/1.00  --sat_fm_uc_incr                        true
% 1.83/1.00  --sat_out_model                         small
% 1.83/1.00  --sat_out_clauses                       false
% 1.83/1.00  
% 1.83/1.00  ------ QBF Options
% 1.83/1.00  
% 1.83/1.00  --qbf_mode                              false
% 1.83/1.00  --qbf_elim_univ                         false
% 1.83/1.00  --qbf_dom_inst                          none
% 1.83/1.00  --qbf_dom_pre_inst                      false
% 1.83/1.00  --qbf_sk_in                             false
% 1.83/1.00  --qbf_pred_elim                         true
% 1.83/1.00  --qbf_split                             512
% 1.83/1.00  
% 1.83/1.00  ------ BMC1 Options
% 1.83/1.00  
% 1.83/1.00  --bmc1_incremental                      false
% 1.83/1.00  --bmc1_axioms                           reachable_all
% 1.83/1.00  --bmc1_min_bound                        0
% 1.83/1.00  --bmc1_max_bound                        -1
% 1.83/1.00  --bmc1_max_bound_default                -1
% 1.83/1.00  --bmc1_symbol_reachability              true
% 1.83/1.00  --bmc1_property_lemmas                  false
% 1.83/1.00  --bmc1_k_induction                      false
% 1.83/1.00  --bmc1_non_equiv_states                 false
% 1.83/1.00  --bmc1_deadlock                         false
% 1.83/1.00  --bmc1_ucm                              false
% 1.83/1.00  --bmc1_add_unsat_core                   none
% 1.83/1.00  --bmc1_unsat_core_children              false
% 1.83/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.83/1.00  --bmc1_out_stat                         full
% 1.83/1.00  --bmc1_ground_init                      false
% 1.83/1.00  --bmc1_pre_inst_next_state              false
% 1.83/1.00  --bmc1_pre_inst_state                   false
% 1.83/1.00  --bmc1_pre_inst_reach_state             false
% 1.83/1.00  --bmc1_out_unsat_core                   false
% 1.83/1.00  --bmc1_aig_witness_out                  false
% 1.83/1.00  --bmc1_verbose                          false
% 1.83/1.00  --bmc1_dump_clauses_tptp                false
% 1.83/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.83/1.00  --bmc1_dump_file                        -
% 1.83/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.83/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.83/1.00  --bmc1_ucm_extend_mode                  1
% 1.83/1.00  --bmc1_ucm_init_mode                    2
% 1.83/1.00  --bmc1_ucm_cone_mode                    none
% 1.83/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.83/1.00  --bmc1_ucm_relax_model                  4
% 1.83/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.83/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.83/1.00  --bmc1_ucm_layered_model                none
% 1.83/1.00  --bmc1_ucm_max_lemma_size               10
% 1.83/1.00  
% 1.83/1.00  ------ AIG Options
% 1.83/1.00  
% 1.83/1.00  --aig_mode                              false
% 1.83/1.00  
% 1.83/1.00  ------ Instantiation Options
% 1.83/1.00  
% 1.83/1.00  --instantiation_flag                    true
% 1.83/1.00  --inst_sos_flag                         false
% 1.83/1.00  --inst_sos_phase                        true
% 1.83/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.83/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.83/1.00  --inst_lit_sel_side                     none
% 1.83/1.00  --inst_solver_per_active                1400
% 1.83/1.00  --inst_solver_calls_frac                1.
% 1.83/1.00  --inst_passive_queue_type               priority_queues
% 1.83/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.83/1.00  --inst_passive_queues_freq              [25;2]
% 1.83/1.00  --inst_dismatching                      true
% 1.83/1.00  --inst_eager_unprocessed_to_passive     true
% 1.83/1.00  --inst_prop_sim_given                   true
% 1.83/1.00  --inst_prop_sim_new                     false
% 1.83/1.00  --inst_subs_new                         false
% 1.83/1.00  --inst_eq_res_simp                      false
% 1.83/1.00  --inst_subs_given                       false
% 1.83/1.00  --inst_orphan_elimination               true
% 1.83/1.00  --inst_learning_loop_flag               true
% 1.83/1.00  --inst_learning_start                   3000
% 1.83/1.00  --inst_learning_factor                  2
% 1.83/1.00  --inst_start_prop_sim_after_learn       3
% 1.83/1.00  --inst_sel_renew                        solver
% 1.83/1.00  --inst_lit_activity_flag                true
% 1.83/1.00  --inst_restr_to_given                   false
% 1.83/1.00  --inst_activity_threshold               500
% 1.83/1.00  --inst_out_proof                        true
% 1.83/1.00  
% 1.83/1.00  ------ Resolution Options
% 1.83/1.00  
% 1.83/1.00  --resolution_flag                       false
% 1.83/1.00  --res_lit_sel                           adaptive
% 1.83/1.00  --res_lit_sel_side                      none
% 1.83/1.00  --res_ordering                          kbo
% 1.83/1.00  --res_to_prop_solver                    active
% 1.83/1.00  --res_prop_simpl_new                    false
% 1.83/1.00  --res_prop_simpl_given                  true
% 1.83/1.00  --res_passive_queue_type                priority_queues
% 1.83/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.83/1.00  --res_passive_queues_freq               [15;5]
% 1.83/1.00  --res_forward_subs                      full
% 1.83/1.00  --res_backward_subs                     full
% 1.83/1.00  --res_forward_subs_resolution           true
% 1.83/1.00  --res_backward_subs_resolution          true
% 1.83/1.00  --res_orphan_elimination                true
% 1.83/1.00  --res_time_limit                        2.
% 1.83/1.00  --res_out_proof                         true
% 1.83/1.00  
% 1.83/1.00  ------ Superposition Options
% 1.83/1.00  
% 1.83/1.00  --superposition_flag                    true
% 1.83/1.00  --sup_passive_queue_type                priority_queues
% 1.83/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.83/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.83/1.00  --demod_completeness_check              fast
% 1.83/1.00  --demod_use_ground                      true
% 1.83/1.00  --sup_to_prop_solver                    passive
% 1.83/1.00  --sup_prop_simpl_new                    true
% 1.83/1.00  --sup_prop_simpl_given                  true
% 1.83/1.00  --sup_fun_splitting                     false
% 1.83/1.00  --sup_smt_interval                      50000
% 1.83/1.00  
% 1.83/1.00  ------ Superposition Simplification Setup
% 1.83/1.00  
% 1.83/1.00  --sup_indices_passive                   []
% 1.83/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.83/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.83/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_full_bw                           [BwDemod]
% 1.83/1.00  --sup_immed_triv                        [TrivRules]
% 1.83/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.83/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_immed_bw_main                     []
% 1.83/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.83/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.83/1.00  
% 1.83/1.00  ------ Combination Options
% 1.83/1.00  
% 1.83/1.00  --comb_res_mult                         3
% 1.83/1.00  --comb_sup_mult                         2
% 1.83/1.00  --comb_inst_mult                        10
% 1.83/1.00  
% 1.83/1.00  ------ Debug Options
% 1.83/1.00  
% 1.83/1.00  --dbg_backtrace                         false
% 1.83/1.00  --dbg_dump_prop_clauses                 false
% 1.83/1.00  --dbg_dump_prop_clauses_file            -
% 1.83/1.00  --dbg_out_stat                          false
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  ------ Proving...
% 1.83/1.00  
% 1.83/1.00  
% 1.83/1.00  % SZS status Theorem for theBenchmark.p
% 1.83/1.00  
% 1.83/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.83/1.00  
% 1.83/1.00  fof(f14,conjecture,(
% 1.83/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.00  
% 1.83/1.00  fof(f15,negated_conjecture,(
% 1.83/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.83/1.00    inference(negated_conjecture,[],[f14])).
% 1.83/1.00  
% 1.83/1.00  fof(f39,plain,(
% 1.83/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.83/1.00    inference(ennf_transformation,[],[f15])).
% 1.83/1.00  
% 1.83/1.00  fof(f40,plain,(
% 1.83/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.83/1.00    inference(flattening,[],[f39])).
% 1.83/1.00  
% 1.83/1.00  fof(f47,plain,(
% 1.83/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) => (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3)) & r3_binop_1(X0,X2,sK3) & m2_filter_1(sK3,X0,X1))) )),
% 1.83/1.00    introduced(choice_axiom,[])).
% 1.83/1.00  
% 1.83/1.00  fof(f46,plain,(
% 1.83/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,sK2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(sK2,X0))) )),
% 1.83/1.00    introduced(choice_axiom,[])).
% 1.83/1.00  
% 1.83/1.00  fof(f45,plain,(
% 1.83/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,sK1)) & m1_subset_1(X2,X0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,X0))) )),
% 1.83/1.00    introduced(choice_axiom,[])).
% 1.83/1.00  
% 1.83/1.00  fof(f44,plain,(
% 1.83/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.83/1.00    introduced(choice_axiom,[])).
% 1.83/1.00  
% 1.83/1.00  fof(f48,plain,(
% 1.83/1.00    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f47,f46,f45,f44])).
% 1.83/1.00  
% 1.83/1.00  fof(f70,plain,(
% 1.83/1.00    v1_partfun1(sK1,sK0)),
% 1.83/1.00    inference(cnf_transformation,[],[f48])).
% 1.83/1.00  
% 1.83/1.00  fof(f3,axiom,(
% 1.83/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f18,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.83/1.01    inference(ennf_transformation,[],[f3])).
% 1.83/1.01  
% 1.83/1.01  fof(f19,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f18])).
% 1.83/1.01  
% 1.83/1.01  fof(f41,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.83/1.01    inference(nnf_transformation,[],[f19])).
% 1.83/1.01  
% 1.83/1.01  fof(f51,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f41])).
% 1.83/1.01  
% 1.83/1.01  fof(f7,axiom,(
% 1.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f26,plain,(
% 1.83/1.01    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.83/1.01    inference(ennf_transformation,[],[f7])).
% 1.83/1.01  
% 1.83/1.01  fof(f27,plain,(
% 1.83/1.01    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f26])).
% 1.83/1.01  
% 1.83/1.01  fof(f60,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f27])).
% 1.83/1.01  
% 1.83/1.01  fof(f6,axiom,(
% 1.83/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_eqrel_1(k8_eqrel_1(X0,X1),X0))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f24,plain,(
% 1.83/1.01    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.83/1.01    inference(ennf_transformation,[],[f6])).
% 1.83/1.01  
% 1.83/1.01  fof(f25,plain,(
% 1.83/1.01    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.83/1.01    inference(flattening,[],[f24])).
% 1.83/1.01  
% 1.83/1.01  fof(f59,plain,(
% 1.83/1.01    ( ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f25])).
% 1.83/1.01  
% 1.83/1.01  fof(f8,axiom,(
% 1.83/1.01    ! [X0,X1] : (m1_eqrel_1(X1,X0) => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f28,plain,(
% 1.83/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0))),
% 1.83/1.01    inference(ennf_transformation,[],[f8])).
% 1.83/1.01  
% 1.83/1.01  fof(f61,plain,(
% 1.83/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f28])).
% 1.83/1.01  
% 1.83/1.01  fof(f72,plain,(
% 1.83/1.01    v8_relat_2(sK1)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f71,plain,(
% 1.83/1.01    v3_relat_2(sK1)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f69,plain,(
% 1.83/1.01    ~v1_xboole_0(sK0)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f73,plain,(
% 1.83/1.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f1,axiom,(
% 1.83/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f16,plain,(
% 1.83/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.83/1.01    inference(ennf_transformation,[],[f1])).
% 1.83/1.01  
% 1.83/1.01  fof(f49,plain,(
% 1.83/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f16])).
% 1.83/1.01  
% 1.83/1.01  fof(f5,axiom,(
% 1.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f22,plain,(
% 1.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 1.83/1.01    inference(ennf_transformation,[],[f5])).
% 1.83/1.01  
% 1.83/1.01  fof(f23,plain,(
% 1.83/1.01    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f22])).
% 1.83/1.01  
% 1.83/1.01  fof(f56,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (v1_funct_1(k3_filter_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f23])).
% 1.83/1.01  
% 1.83/1.01  fof(f57,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f23])).
% 1.83/1.01  
% 1.83/1.01  fof(f58,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f23])).
% 1.83/1.01  
% 1.83/1.01  fof(f12,axiom,(
% 1.83/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f35,plain,(
% 1.83/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.83/1.01    inference(ennf_transformation,[],[f12])).
% 1.83/1.01  
% 1.83/1.01  fof(f36,plain,(
% 1.83/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f35])).
% 1.83/1.01  
% 1.83/1.01  fof(f67,plain,(
% 1.83/1.01    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f36])).
% 1.83/1.01  
% 1.83/1.01  fof(f75,plain,(
% 1.83/1.01    m2_filter_1(sK3,sK0,sK1)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f13,axiom,(
% 1.83/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f37,plain,(
% 1.83/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.83/1.01    inference(ennf_transformation,[],[f13])).
% 1.83/1.01  
% 1.83/1.01  fof(f38,plain,(
% 1.83/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f37])).
% 1.83/1.01  
% 1.83/1.01  fof(f68,plain,(
% 1.83/1.01    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f38])).
% 1.83/1.01  
% 1.83/1.01  fof(f10,axiom,(
% 1.83/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f31,plain,(
% 1.83/1.01    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.83/1.01    inference(ennf_transformation,[],[f10])).
% 1.83/1.01  
% 1.83/1.01  fof(f32,plain,(
% 1.83/1.01    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f31])).
% 1.83/1.01  
% 1.83/1.01  fof(f65,plain,(
% 1.83/1.01    ( ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f32])).
% 1.83/1.01  
% 1.83/1.01  fof(f11,axiom,(
% 1.83/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f33,plain,(
% 1.83/1.01    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.83/1.01    inference(ennf_transformation,[],[f11])).
% 1.83/1.01  
% 1.83/1.01  fof(f34,plain,(
% 1.83/1.01    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.83/1.01    inference(flattening,[],[f33])).
% 1.83/1.01  
% 1.83/1.01  fof(f66,plain,(
% 1.83/1.01    ( ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f34])).
% 1.83/1.01  
% 1.83/1.01  fof(f4,axiom,(
% 1.83/1.01    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f20,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 1.83/1.01    inference(ennf_transformation,[],[f4])).
% 1.83/1.01  
% 1.83/1.01  fof(f21,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.83/1.01    inference(flattening,[],[f20])).
% 1.83/1.01  
% 1.83/1.01  fof(f42,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.83/1.01    inference(nnf_transformation,[],[f21])).
% 1.83/1.01  
% 1.83/1.01  fof(f43,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.83/1.01    inference(flattening,[],[f42])).
% 1.83/1.01  
% 1.83/1.01  fof(f54,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f43])).
% 1.83/1.01  
% 1.83/1.01  fof(f76,plain,(
% 1.83/1.01    r3_binop_1(sK0,sK2,sK3)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f53,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f43])).
% 1.83/1.01  
% 1.83/1.01  fof(f55,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f43])).
% 1.83/1.01  
% 1.83/1.01  fof(f77,plain,(
% 1.83/1.01    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  fof(f2,axiom,(
% 1.83/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f17,plain,(
% 1.83/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/1.01    inference(ennf_transformation,[],[f2])).
% 1.83/1.01  
% 1.83/1.01  fof(f50,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.83/1.01    inference(cnf_transformation,[],[f17])).
% 1.83/1.01  
% 1.83/1.01  fof(f9,axiom,(
% 1.83/1.01    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 1.83/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.83/1.01  
% 1.83/1.01  fof(f29,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 1.83/1.01    inference(ennf_transformation,[],[f9])).
% 1.83/1.01  
% 1.83/1.01  fof(f30,plain,(
% 1.83/1.01    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 1.83/1.01    inference(flattening,[],[f29])).
% 1.83/1.01  
% 1.83/1.01  fof(f62,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f30])).
% 1.83/1.01  
% 1.83/1.01  fof(f63,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f30])).
% 1.83/1.01  
% 1.83/1.01  fof(f64,plain,(
% 1.83/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.83/1.01    inference(cnf_transformation,[],[f30])).
% 1.83/1.01  
% 1.83/1.01  fof(f74,plain,(
% 1.83/1.01    m1_subset_1(sK2,sK0)),
% 1.83/1.01    inference(cnf_transformation,[],[f48])).
% 1.83/1.01  
% 1.83/1.01  cnf(c_27,negated_conjecture,
% 1.83/1.01      ( v1_partfun1(sK1,sK0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_3,plain,
% 1.83/1.01      ( ~ m2_subset_1(X0,X1,X2)
% 1.83/1.01      | m1_subset_1(X0,X2)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(X2) ),
% 1.83/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_11,plain,
% 1.83/1.01      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
% 1.83/1.01      | ~ v1_partfun1(X1,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(X1)
% 1.83/1.01      | ~ v8_relat_2(X1)
% 1.83/1.01      | v1_xboole_0(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_416,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | m1_subset_1(X3,X4)
% 1.83/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X5)
% 1.83/1.01      | v1_xboole_0(X4)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | k9_eqrel_1(X1,X0,X2) != X3
% 1.83/1.01      | k8_eqrel_1(X1,X0) != X4
% 1.83/1.01      | k1_zfmisc_1(X1) != X5 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_417,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.83/1.01      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_416]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_10,plain,
% 1.83/1.01      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
% 1.83/1.01      | ~ v1_partfun1(X1,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(X1)
% 1.83/1.01      | ~ v8_relat_2(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_12,plain,
% 1.83/1.01      ( ~ m1_eqrel_1(X0,X1)
% 1.83/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 1.83/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_322,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | X3 != X1
% 1.83/1.01      | k8_eqrel_1(X1,X0) != X2 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_323,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_322]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_421,plain,
% 1.83/1.01      ( m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_417,c_323]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_422,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_421]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_25,negated_conjecture,
% 1.83/1.01      ( v8_relat_2(sK1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_681,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X1))
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_422,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_682,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,X0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_681]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_26,negated_conjecture,
% 1.83/1.01      ( v3_relat_2(sK1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_686,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.83/1.01      | ~ m1_subset_1(X1,X0)
% 1.83/1.01      | ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_682,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_687,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,X0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_686]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_954,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,X1)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(X1,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(X1))
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_687]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_955,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(sK0))
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_954]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_28,negated_conjecture,
% 1.83/1.01      ( ~ v1_xboole_0(sK0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_24,negated_conjecture,
% 1.83/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.83/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_959,plain,
% 1.83/1.01      ( v1_xboole_0(k1_zfmisc_1(sK0))
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_955,c_28,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_960,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(sK0)) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_959]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1198,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ sP0_iProver_split ),
% 1.83/1.01      inference(splitting,
% 1.83/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.83/1.01                [c_960]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1911,plain,
% 1.83/1.01      ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(sK2,sK0)
% 1.83/1.01      | ~ sP0_iProver_split ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_1198]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_0,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.83/1.01      | ~ v1_xboole_0(X1)
% 1.83/1.01      | v1_xboole_0(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1755,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1863,plain,
% 1.83/1.01      ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.83/1.01      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_1755]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_9,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v8_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_780,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != X2 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_781,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_780]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_785,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_781,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_786,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_785]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1026,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_786]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1027,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_1026]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1031,plain,
% 1.83/1.01      ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_1027,c_28,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1032,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_1031]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1743,plain,
% 1.83/1.01      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ v1_funct_1(sK3) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_1032]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_8,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v8_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_813,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != X2 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_814,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_813]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_818,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_814,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_819,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_818]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1002,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_819]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1003,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_1002]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1007,plain,
% 1.83/1.01      ( ~ v1_funct_1(X0)
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_1003,c_28,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1008,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_funct_1(X0) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_1007]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1744,plain,
% 1.83/1.01      ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_funct_1(sK3) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_1008]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_7,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v8_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_846,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != X2 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_847,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_846]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_851,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_847,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_852,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_partfun1(sK1,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_851]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_978,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_852]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_979,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_978]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_983,plain,
% 1.83/1.01      ( ~ v1_funct_1(X0)
% 1.83/1.01      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_979,c_28,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_984,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.83/1.01      | ~ v1_funct_1(X0) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_983]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1745,plain,
% 1.83/1.01      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_funct_1(sK3) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_984]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_18,plain,
% 1.83/1.01      ( ~ m2_filter_1(X0,X1,X2)
% 1.83/1.01      | ~ r1_binop_1(X1,X3,X0)
% 1.83/1.01      | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X3,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v8_relat_2(X2)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_22,negated_conjecture,
% 1.83/1.01      ( m2_filter_1(sK3,sK0,sK1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_486,plain,
% 1.83/1.01      ( ~ r1_binop_1(X0,X1,X2)
% 1.83/1.01      | r1_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.83/1.01      | ~ v1_partfun1(X3,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,X0)
% 1.83/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(X3)
% 1.83/1.01      | ~ v8_relat_2(X3)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | sK3 != X2
% 1.83/1.01      | sK1 != X3
% 1.83/1.01      | sK0 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_487,plain,
% 1.83/1.01      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r1_binop_1(sK0,X0,sK3)
% 1.83/1.01      | ~ v1_partfun1(sK1,sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v8_relat_2(sK1)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_486]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_491,plain,
% 1.83/1.01      ( ~ r1_binop_1(sK0,X0,sK3)
% 1.83/1.01      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ m1_subset_1(X0,sK0) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_487,c_28,c_27,c_26,c_25,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_492,plain,
% 1.83/1.01      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r1_binop_1(sK0,X0,sK3)
% 1.83/1.01      | ~ m1_subset_1(X0,sK0) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_491]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1740,plain,
% 1.83/1.01      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r1_binop_1(sK0,sK2,sK3)
% 1.83/1.01      | ~ m1_subset_1(sK2,sK0) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_492]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_19,plain,
% 1.83/1.01      ( ~ m2_filter_1(X0,X1,X2)
% 1.83/1.01      | ~ r2_binop_1(X1,X3,X0)
% 1.83/1.01      | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.83/1.01      | ~ v1_partfun1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X3,X1)
% 1.83/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X2)
% 1.83/1.01      | ~ v8_relat_2(X2)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_465,plain,
% 1.83/1.01      ( ~ r2_binop_1(X0,X1,X2)
% 1.83/1.01      | r2_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.83/1.01      | ~ v1_partfun1(X3,X0)
% 1.83/1.01      | ~ m1_subset_1(X1,X0)
% 1.83/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(X3)
% 1.83/1.01      | ~ v8_relat_2(X3)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | sK3 != X2
% 1.83/1.01      | sK1 != X3
% 1.83/1.01      | sK0 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_466,plain,
% 1.83/1.01      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r2_binop_1(sK0,X0,sK3)
% 1.83/1.01      | ~ v1_partfun1(sK1,sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v8_relat_2(sK1)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_465]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_470,plain,
% 1.83/1.01      ( ~ r2_binop_1(sK0,X0,sK3)
% 1.83/1.01      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ m1_subset_1(X0,sK0) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_466,c_28,c_27,c_26,c_25,c_24]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_471,plain,
% 1.83/1.01      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r2_binop_1(sK0,X0,sK3)
% 1.83/1.01      | ~ m1_subset_1(X0,sK0) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_470]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1737,plain,
% 1.83/1.01      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r2_binop_1(sK0,sK2,sK3)
% 1.83/1.01      | ~ m1_subset_1(sK2,sK0) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_471]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_16,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
% 1.83/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_756,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_757,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_756]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_761,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_757,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_762,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_761]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_924,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | v1_xboole_0(X0)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_762]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_925,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_924]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_759,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_757]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_927,plain,
% 1.83/1.01      ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_925,c_28,c_27,c_26,c_24,c_759]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1581,plain,
% 1.83/1.01      ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.83/1.01      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_17,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | ~ v8_relat_2(X0)
% 1.83/1.01      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_735,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_736,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_735]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_740,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_736,c_26]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_741,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_740]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_935,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
% 1.83/1.01      | sK1 != sK1
% 1.83/1.01      | sK0 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_741]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_936,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_935]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_738,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v3_relat_2(sK1)
% 1.83/1.01      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_736]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_938,plain,
% 1.83/1.01      ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_936,c_27,c_26,c_24,c_738]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1606,plain,
% 1.83/1.01      ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.83/1.01      inference(light_normalisation,[status(thm)],[c_1581,c_938]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1697,plain,
% 1.83/1.01      ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
% 1.83/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1606]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1199,plain,
% 1.83/1.01      ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | v1_xboole_0(k1_zfmisc_1(sK0))
% 1.83/1.01      | sP0_iProver_split ),
% 1.83/1.01      inference(splitting,
% 1.83/1.01                [splitting(split),new_symbols(definition,[])],
% 1.83/1.01                [c_960]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_714,plain,
% 1.83/1.01      ( ~ v1_partfun1(X0,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.83/1.01      | m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.83/1.01      | ~ v3_relat_2(X0)
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_323,c_25]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_715,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,X0)
% 1.83/1.01      | m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.83/1.01      | ~ v3_relat_2(sK1) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_714]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_717,plain,
% 1.83/1.01      ( ~ v1_partfun1(sK1,sK0)
% 1.83/1.01      | m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | ~ v3_relat_2(sK1) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_715]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_5,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | r2_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ r3_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_21,negated_conjecture,
% 1.83/1.01      ( r3_binop_1(sK0,sK2,sK3) ),
% 1.83/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_646,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | r2_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | sK3 != X0
% 1.83/1.01      | sK2 != X2
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_647,plain,
% 1.83/1.01      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | r2_binop_1(sK0,sK2,sK3)
% 1.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK2,sK0)
% 1.83/1.01      | ~ v1_funct_1(sK3) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_646]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_6,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | r1_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ r3_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_635,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | r1_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | sK3 != X0
% 1.83/1.01      | sK2 != X2
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_636,plain,
% 1.83/1.01      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | r1_binop_1(sK0,sK2,sK3)
% 1.83/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK2,sK0)
% 1.83/1.01      | ~ v1_funct_1(sK3) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_635]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_4,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ r1_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ r2_binop_1(X1,X2,X0)
% 1.83/1.01      | r3_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_20,negated_conjecture,
% 1.83/1.01      ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
% 1.83/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_613,plain,
% 1.83/1.01      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ r1_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ r2_binop_1(X1,X2,X0)
% 1.83/1.01      | ~ m1_subset_1(X2,X1)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_funct_1(X0)
% 1.83/1.01      | k9_eqrel_1(sK0,sK1,sK2) != X2
% 1.83/1.01      | k3_filter_1(sK0,sK1,sK3) != X0
% 1.83/1.01      | k8_eqrel_1(sK0,sK1) != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_614,plain,
% 1.83/1.01      ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.83/1.01      | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.83/1.01      | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.83/1.01      | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_613]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_1,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.01      | v1_relat_1(X0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_15,plain,
% 1.83/1.01      ( ~ m2_filter_1(X0,X1,X2)
% 1.83/1.01      | v1_funct_1(X0)
% 1.83/1.01      | ~ v1_relat_1(X2)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_507,plain,
% 1.83/1.01      ( v1_funct_1(X0)
% 1.83/1.01      | ~ v1_relat_1(X1)
% 1.83/1.01      | v1_xboole_0(X2)
% 1.83/1.01      | sK3 != X0
% 1.83/1.01      | sK1 != X1
% 1.83/1.01      | sK0 != X2 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_508,plain,
% 1.83/1.01      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_507]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_510,plain,
% 1.83/1.01      ( ~ v1_relat_1(sK1) | v1_funct_1(sK3) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_508,c_28]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_511,plain,
% 1.83/1.01      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_510]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_592,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.01      | v1_funct_1(sK3)
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_511]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_593,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.83/1.01      | v1_funct_1(sK3) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_592]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_595,plain,
% 1.83/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.83/1.01      | v1_funct_1(sK3) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_593]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_14,plain,
% 1.83/1.01      ( ~ m2_filter_1(X0,X1,X2)
% 1.83/1.01      | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_relat_1(X2)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_521,plain,
% 1.83/1.01      ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.83/1.01      | ~ v1_relat_1(X2)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK3 != X0
% 1.83/1.01      | sK1 != X2
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_522,plain,
% 1.83/1.01      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ v1_relat_1(sK1)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_521]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_524,plain,
% 1.83/1.01      ( ~ v1_relat_1(sK1) | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_522,c_28]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_525,plain,
% 1.83/1.01      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~ v1_relat_1(sK1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_524]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_579,plain,
% 1.83/1.01      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_525]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_580,plain,
% 1.83/1.01      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_579]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_582,plain,
% 1.83/1.01      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_580]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_13,plain,
% 1.83/1.01      ( ~ m2_filter_1(X0,X1,X2)
% 1.83/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_relat_1(X2)
% 1.83/1.01      | v1_xboole_0(X1) ),
% 1.83/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_535,plain,
% 1.83/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.83/1.01      | ~ v1_relat_1(X2)
% 1.83/1.01      | v1_xboole_0(X1)
% 1.83/1.01      | sK3 != X0
% 1.83/1.01      | sK1 != X2
% 1.83/1.01      | sK0 != X1 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_536,plain,
% 1.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_relat_1(sK1)
% 1.83/1.01      | v1_xboole_0(sK0) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_535]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_538,plain,
% 1.83/1.01      ( ~ v1_relat_1(sK1)
% 1.83/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.83/1.01      inference(global_propositional_subsumption,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_536,c_28]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_539,plain,
% 1.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ v1_relat_1(sK1) ),
% 1.83/1.01      inference(renaming,[status(thm)],[c_538]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_566,plain,
% 1.83/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | sK1 != X0 ),
% 1.83/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_539]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_567,plain,
% 1.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.83/1.01      inference(unflattening,[status(thm)],[c_566]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_569,plain,
% 1.83/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.83/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.83/1.01      inference(instantiation,[status(thm)],[c_567]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(c_23,negated_conjecture,
% 1.83/1.01      ( m1_subset_1(sK2,sK0) ),
% 1.83/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.83/1.01  
% 1.83/1.01  cnf(contradiction,plain,
% 1.83/1.01      ( $false ),
% 1.83/1.01      inference(minisat,
% 1.83/1.01                [status(thm)],
% 1.83/1.01                [c_1911,c_1863,c_1743,c_1744,c_1745,c_1740,c_1737,c_1697,
% 1.83/1.01                 c_1199,c_717,c_647,c_636,c_614,c_595,c_582,c_569,c_23,
% 1.83/1.01                 c_24,c_26,c_27]) ).
% 1.83/1.01  
% 1.83/1.01  
% 1.83/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.83/1.01  
% 1.83/1.01  ------                               Statistics
% 1.83/1.01  
% 1.83/1.01  ------ General
% 1.83/1.01  
% 1.83/1.01  abstr_ref_over_cycles:                  0
% 1.83/1.01  abstr_ref_under_cycles:                 0
% 1.83/1.01  gc_basic_clause_elim:                   0
% 1.83/1.01  forced_gc_time:                         0
% 1.83/1.01  parsing_time:                           0.017
% 1.83/1.01  unif_index_cands_time:                  0.
% 1.83/1.01  unif_index_add_time:                    0.
% 1.83/1.01  orderings_time:                         0.
% 1.83/1.01  out_proof_time:                         0.017
% 1.83/1.01  total_time:                             0.108
% 1.83/1.01  num_of_symbols:                         56
% 1.83/1.01  num_of_terms:                           1226
% 1.83/1.01  
% 1.83/1.01  ------ Preprocessing
% 1.83/1.01  
% 1.83/1.01  num_of_splits:                          1
% 1.83/1.01  num_of_split_atoms:                     1
% 1.83/1.01  num_of_reused_defs:                     0
% 1.83/1.01  num_eq_ax_congr_red:                    4
% 1.83/1.01  num_of_sem_filtered_clauses:            1
% 1.83/1.01  num_of_subtypes:                        1
% 1.83/1.01  monotx_restored_types:                  0
% 1.83/1.01  sat_num_of_epr_types:                   0
% 1.83/1.01  sat_num_of_non_cyclic_types:            0
% 1.83/1.01  sat_guarded_non_collapsed_types:        0
% 1.83/1.01  num_pure_diseq_elim:                    0
% 1.83/1.01  simp_replaced_by:                       0
% 1.83/1.01  res_preprocessed:                       120
% 1.83/1.01  prep_upred:                             0
% 1.83/1.01  prep_unflattend:                        49
% 1.83/1.01  smt_new_axioms:                         0
% 1.83/1.01  pred_elim_cands:                        6
% 1.83/1.01  pred_elim:                              8
% 1.83/1.01  pred_elim_cl:                           9
% 1.83/1.01  pred_elim_cycles:                       11
% 1.83/1.01  merged_defs:                            0
% 1.83/1.01  merged_defs_ncl:                        0
% 1.83/1.01  bin_hyper_res:                          0
% 1.83/1.01  prep_cycles:                            4
% 1.83/1.01  pred_elim_time:                         0.018
% 1.83/1.01  splitting_time:                         0.
% 1.83/1.01  sem_filter_time:                        0.
% 1.83/1.01  monotx_time:                            0.
% 1.83/1.01  subtype_inf_time:                       0.
% 1.83/1.01  
% 1.83/1.01  ------ Problem properties
% 1.83/1.01  
% 1.83/1.01  clauses:                                21
% 1.83/1.01  conjectures:                            3
% 1.83/1.01  epr:                                    5
% 1.83/1.01  horn:                                   20
% 1.83/1.01  ground:                                 14
% 1.83/1.01  unary:                                  11
% 1.83/1.01  binary:                                 0
% 1.83/1.01  lits:                                   47
% 1.83/1.01  lits_eq:                                4
% 1.83/1.01  fd_pure:                                0
% 1.83/1.01  fd_pseudo:                              0
% 1.83/1.01  fd_cond:                                0
% 1.83/1.01  fd_pseudo_cond:                         0
% 1.83/1.01  ac_symbols:                             0
% 1.83/1.01  
% 1.83/1.01  ------ Propositional Solver
% 1.83/1.01  
% 1.83/1.01  prop_solver_calls:                      24
% 1.83/1.01  prop_fast_solver_calls:                 975
% 1.83/1.01  smt_solver_calls:                       0
% 1.83/1.01  smt_fast_solver_calls:                  0
% 1.83/1.01  prop_num_of_clauses:                    422
% 1.83/1.01  prop_preprocess_simplified:             2909
% 1.83/1.01  prop_fo_subsumed:                       44
% 1.83/1.01  prop_solver_time:                       0.
% 1.83/1.01  smt_solver_time:                        0.
% 1.83/1.01  smt_fast_solver_time:                   0.
% 1.83/1.01  prop_fast_solver_time:                  0.
% 1.83/1.01  prop_unsat_core_time:                   0.
% 1.83/1.01  
% 1.83/1.01  ------ QBF
% 1.83/1.01  
% 1.83/1.01  qbf_q_res:                              0
% 1.83/1.01  qbf_num_tautologies:                    0
% 1.83/1.01  qbf_prep_cycles:                        0
% 1.83/1.01  
% 1.83/1.01  ------ BMC1
% 1.83/1.01  
% 1.83/1.01  bmc1_current_bound:                     -1
% 1.83/1.01  bmc1_last_solved_bound:                 -1
% 1.83/1.01  bmc1_unsat_core_size:                   -1
% 1.83/1.01  bmc1_unsat_core_parents_size:           -1
% 1.83/1.01  bmc1_merge_next_fun:                    0
% 1.83/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.83/1.01  
% 1.83/1.01  ------ Instantiation
% 1.83/1.01  
% 1.83/1.01  inst_num_of_clauses:                    76
% 1.83/1.01  inst_num_in_passive:                    21
% 1.83/1.01  inst_num_in_active:                     52
% 1.83/1.01  inst_num_in_unprocessed:                2
% 1.83/1.01  inst_num_of_loops:                      57
% 1.83/1.01  inst_num_of_learning_restarts:          0
% 1.83/1.01  inst_num_moves_active_passive:          3
% 1.83/1.01  inst_lit_activity:                      0
% 1.83/1.01  inst_lit_activity_moves:                0
% 1.83/1.01  inst_num_tautologies:                   0
% 1.83/1.01  inst_num_prop_implied:                  0
% 1.83/1.01  inst_num_existing_simplified:           0
% 1.83/1.01  inst_num_eq_res_simplified:             0
% 1.83/1.01  inst_num_child_elim:                    0
% 1.83/1.01  inst_num_of_dismatching_blockings:      0
% 1.83/1.01  inst_num_of_non_proper_insts:           29
% 1.83/1.01  inst_num_of_duplicates:                 0
% 1.83/1.01  inst_inst_num_from_inst_to_res:         0
% 1.83/1.01  inst_dismatching_checking_time:         0.
% 1.83/1.01  
% 1.83/1.01  ------ Resolution
% 1.83/1.01  
% 1.83/1.01  res_num_of_clauses:                     0
% 1.83/1.01  res_num_in_passive:                     0
% 1.83/1.01  res_num_in_active:                      0
% 1.83/1.01  res_num_of_loops:                       124
% 1.83/1.01  res_forward_subset_subsumed:            0
% 1.83/1.01  res_backward_subset_subsumed:           0
% 1.83/1.01  res_forward_subsumed:                   0
% 1.83/1.01  res_backward_subsumed:                  0
% 1.83/1.01  res_forward_subsumption_resolution:     0
% 1.83/1.01  res_backward_subsumption_resolution:    0
% 1.83/1.01  res_clause_to_clause_subsumption:       33
% 1.83/1.01  res_orphan_elimination:                 0
% 1.83/1.01  res_tautology_del:                      8
% 1.83/1.01  res_num_eq_res_simplified:              0
% 1.83/1.01  res_num_sel_changes:                    0
% 1.83/1.01  res_moves_from_active_to_pass:          0
% 1.83/1.01  
% 1.83/1.01  ------ Superposition
% 1.83/1.01  
% 1.83/1.01  sup_time_total:                         0.
% 1.83/1.01  sup_time_generating:                    0.
% 1.83/1.01  sup_time_sim_full:                      0.
% 1.83/1.01  sup_time_sim_immed:                     0.
% 1.83/1.01  
% 1.83/1.01  sup_num_of_clauses:                     22
% 1.83/1.01  sup_num_in_active:                      10
% 1.83/1.01  sup_num_in_passive:                     12
% 1.83/1.01  sup_num_of_loops:                       10
% 1.83/1.01  sup_fw_superposition:                   1
% 1.83/1.01  sup_bw_superposition:                   0
% 1.83/1.01  sup_immediate_simplified:               0
% 1.83/1.01  sup_given_eliminated:                   0
% 1.83/1.01  comparisons_done:                       0
% 1.83/1.01  comparisons_avoided:                    0
% 1.83/1.01  
% 1.83/1.01  ------ Simplifications
% 1.83/1.01  
% 1.83/1.01  
% 1.83/1.01  sim_fw_subset_subsumed:                 0
% 1.83/1.01  sim_bw_subset_subsumed:                 0
% 1.83/1.01  sim_fw_subsumed:                        0
% 1.83/1.01  sim_bw_subsumed:                        0
% 1.83/1.01  sim_fw_subsumption_res:                 1
% 1.83/1.01  sim_bw_subsumption_res:                 0
% 1.83/1.01  sim_tautology_del:                      0
% 1.83/1.01  sim_eq_tautology_del:                   0
% 1.83/1.01  sim_eq_res_simp:                        0
% 1.83/1.01  sim_fw_demodulated:                     0
% 1.83/1.01  sim_bw_demodulated:                     0
% 1.83/1.01  sim_light_normalised:                   1
% 1.83/1.01  sim_joinable_taut:                      0
% 1.83/1.01  sim_joinable_simp:                      0
% 1.83/1.01  sim_ac_normalised:                      0
% 1.83/1.01  sim_smt_subsumption:                    0
% 1.83/1.01  
%------------------------------------------------------------------------------
