%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1417+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:40 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 749 expanded)
%              Number of clauses        :   79 ( 152 expanded)
%              Number of leaves         :   11 ( 278 expanded)
%              Depth                    :   15
%              Number of atoms          :  722 (6112 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r6_binop_1(X0,X2,X3)
                   => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r6_binop_1(X0,X2,X3)
                     => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r6_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r6_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
              & r6_binop_1(X0,X2,X3)
              & m2_filter_1(X3,X0,X1) )
          & m2_filter_1(X2,X0,X1) )
     => ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,sK2),k3_filter_1(X0,X1,X3))
            & r6_binop_1(X0,sK2,X3)
            & m2_filter_1(X3,X0,X1) )
        & m2_filter_1(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(X0,sK1),k3_filter_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3))
                & r6_binop_1(X0,X2,X3)
                & m2_filter_1(X3,X0,sK1) )
            & m2_filter_1(X2,X0,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK1)
        & v3_relat_2(sK1)
        & v1_partfun1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r6_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m2_filter_1(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r6_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m2_filter_1(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r6_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m2_filter_1(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27,f26,f25,f24])).

fof(f42,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r5_binop_1(X0,X2,X3)
                   => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r4_binop_1(X0,X2,X3)
                   => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r6_binop_1(X0,X1,X2)
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    m2_filter_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ r5_binop_1(X1,X0,X3)
    | r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_309,plain,
    ( ~ m2_filter_1(X0,X1,sK1)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ r5_binop_1(X1,X0,X2)
    | r5_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_10,c_17])).

cnf(c_18,negated_conjecture,
    ( v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_313,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(sK1,X1)
    | r5_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ r5_binop_1(X1,X0,X2)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ m2_filter_1(X0,X1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_18])).

cnf(c_314,plain,
    ( ~ m2_filter_1(X0,X1,sK1)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ r5_binop_1(X1,X0,X2)
    | r5_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_546,plain,
    ( ~ m2_filter_1(X0,sK0,sK1)
    | ~ m2_filter_1(X1,sK0,sK1)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
    | ~ r5_binop_1(sK0,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[status(thm)],[c_19,c_314])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_550,plain,
    ( ~ m2_filter_1(X0,sK0,sK1)
    | ~ m2_filter_1(X1,sK0,sK1)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
    | ~ r5_binop_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_20,c_16])).

cnf(c_967,plain,
    ( ~ m2_filter_1(X0_48,sK0,sK1)
    | ~ m2_filter_1(X1_48,sK0,sK1)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0_48),k3_filter_1(sK0,sK1,X1_48))
    | ~ r5_binop_1(sK0,X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_550])).

cnf(c_1086,plain,
    ( ~ m2_filter_1(X0_48,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X0_48))
    | ~ r5_binop_1(sK0,sK2,X0_48) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1144,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r5_binop_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_11,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ r4_binop_1(X1,X0,X3)
    | r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_277,plain,
    ( ~ m2_filter_1(X0,X1,sK1)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ r4_binop_1(X1,X0,X2)
    | r4_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_17])).

cnf(c_281,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(sK1,X1)
    | r4_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ r4_binop_1(X1,X0,X2)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ m2_filter_1(X0,X1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_18])).

cnf(c_282,plain,
    ( ~ m2_filter_1(X0,X1,sK1)
    | ~ m2_filter_1(X2,X1,sK1)
    | ~ r4_binop_1(X1,X0,X2)
    | r4_binop_1(k8_eqrel_1(X1,sK1),k3_filter_1(X1,sK1,X0),k3_filter_1(X1,sK1,X2))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_569,plain,
    ( ~ m2_filter_1(X0,sK0,sK1)
    | ~ m2_filter_1(X1,sK0,sK1)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
    | ~ r4_binop_1(sK0,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[status(thm)],[c_19,c_282])).

cnf(c_573,plain,
    ( ~ m2_filter_1(X0,sK0,sK1)
    | ~ m2_filter_1(X1,sK0,sK1)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
    | ~ r4_binop_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_20,c_16])).

cnf(c_966,plain,
    ( ~ m2_filter_1(X0_48,sK0,sK1)
    | ~ m2_filter_1(X1_48,sK0,sK1)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X0_48),k3_filter_1(sK0,sK1,X1_48))
    | ~ r4_binop_1(sK0,X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_1076,plain,
    ( ~ m2_filter_1(X0_48,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X0_48))
    | ~ r4_binop_1(sK0,sK2,X0_48) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1132,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_405,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_17])).

cnf(c_409,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_18])).

cnf(c_410,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_410])).

cnf(c_481,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_20,c_16])).

cnf(c_970,plain,
    ( ~ v1_funct_2(X0_48,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0_48),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_481])).

cnf(c_1100,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_373,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_17])).

cnf(c_377,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_18])).

cnf(c_378,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_500,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_378])).

cnf(c_504,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_20,c_16])).

cnf(c_969,plain,
    ( ~ v1_funct_2(X0_48,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0_48),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_1101,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_341,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0)) ),
    inference(resolution,[status(thm)],[c_6,c_17])).

cnf(c_345,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_18])).

cnf(c_346,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0)) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
    inference(resolution,[status(thm)],[c_19,c_346])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_20,c_16])).

cnf(c_968,plain,
    ( ~ v1_funct_2(X0_48,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0_48)) ),
    inference(subtyping,[status(esa)],[c_527])).

cnf(c_1102,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1091,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_1092,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_1093,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_9,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_xboole_0(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_617,plain,
    ( ~ m2_filter_1(X0,sK0,X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_965,plain,
    ( ~ m2_filter_1(X0_48,sK0,X1_48)
    | v1_funct_1(X0_48)
    | ~ v1_relat_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_1068,plain,
    ( ~ m2_filter_1(sK2,sK0,sK1)
    | v1_funct_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1065,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | v1_funct_1(sK3)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_8,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_631,plain,
    ( ~ m2_filter_1(X0,sK0,X1)
    | v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_964,plain,
    ( ~ m2_filter_1(X0_48,sK0,X1_48)
    | v1_funct_2(X0_48,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_1062,plain,
    ( ~ m2_filter_1(sK2,sK0,sK1)
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_1059,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_7,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_645,plain,
    ( ~ m2_filter_1(X0,sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_963,plain,
    ( ~ m2_filter_1(X0_48,sK0,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_645])).

cnf(c_1056,plain,
    ( ~ m2_filter_1(sK2,sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_1053,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_974,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_976,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | r5_binop_1(X1,X2,X0)
    | ~ r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_775,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | r4_binop_1(X1,X2,X0)
    | ~ r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_751,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ r4_binop_1(X1,X2,X0)
    | ~ r5_binop_1(X1,X2,X0)
    | r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_724,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_12])).

cnf(c_14,negated_conjecture,
    ( m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( m2_filter_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1144,c_1132,c_1100,c_1101,c_1102,c_1091,c_1092,c_1093,c_1068,c_1065,c_1062,c_1059,c_1056,c_1053,c_976,c_775,c_751,c_724,c_14,c_15,c_16])).


%------------------------------------------------------------------------------
