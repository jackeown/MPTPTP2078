%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:56 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  210 (1127 expanded)
%              Number of clauses        :  137 ( 242 expanded)
%              Number of leaves         :   17 ( 413 expanded)
%              Depth                    :   21
%              Number of atoms          : 1093 (8855 expanded)
%              Number of equality atoms :   72 ( 112 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r3_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f46,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f45,f44,f43,f42])).

fof(f67,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

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
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

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
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_739,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_25,negated_conjecture,
    ( v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_744,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_25])).

cnf(c_745,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_744])).

cnf(c_985,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_745])).

cnf(c_986,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_990,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_27,c_23])).

cnf(c_991,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
    inference(renaming,[status(thm)],[c_990])).

cnf(c_1707,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_991])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_772,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_773,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_777,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_25])).

cnf(c_778,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_777])).

cnf(c_961,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_778])).

cnf(c_962,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_966,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_27,c_23])).

cnf(c_967,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_966])).

cnf(c_1708,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_967])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_805,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_806,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_25])).

cnf(c_811,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_810])).

cnf(c_937,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_811])).

cnf(c_938,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_937])).

cnf(c_942,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_27,c_23])).

cnf(c_943,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_942])).

cnf(c_1709,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_17,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r1_binop_1(X1,X3,X0)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_445,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_446,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_450,plain,
    ( ~ r1_binop_1(sK0,X0,sK3)
    | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_27,c_26,c_25,c_24,c_23])).

cnf(c_451,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_1704,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_18,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r2_binop_1(X1,X3,X0)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_424,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_425,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_429,plain,
    ( ~ r2_binop_1(sK0,X0,sK3)
    | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_27,c_26,c_25,c_24,c_23])).

cnf(c_430,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_1701,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_3,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_376,plain,
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

cnf(c_377,plain,
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
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_401,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_377,c_0])).

cnf(c_640,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_24])).

cnf(c_641,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_645,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_25])).

cnf(c_646,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X1,sK1),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,sK1))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_646])).

cnf(c_914,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_918,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_914,c_27,c_23])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_918])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_919])).

cnf(c_1698,plain,
    ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK2,sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1158,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_919])).

cnf(c_1537,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_694,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_695,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_25])).

cnf(c_700,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_700])).

cnf(c_895,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_697,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_897,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_27,c_26,c_25,c_23,c_697])).

cnf(c_1539,plain,
    ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_673,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_674,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_678,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_25])).

cnf(c_679,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_678])).

cnf(c_905,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_679])).

cnf(c_906,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_676,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_908,plain,
    ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_26,c_25,c_23,c_676])).

cnf(c_1565,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1539,c_908])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_718,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_719,plain,
    ( ~ v1_partfun1(sK1,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_723,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ v1_partfun1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_25])).

cnf(c_724,plain,
    ( ~ v1_partfun1(sK1,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(renaming,[status(thm)],[c_723])).

cnf(c_883,plain,
    ( m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_724])).

cnf(c_884,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_721,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_886,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_884,c_26,c_25,c_23,c_721])).

cnf(c_1540,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_1572,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1540,c_908])).

cnf(c_1586,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1537,c_1565,c_1572])).

cnf(c_1658,plain,
    ( sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1586])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_606,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_594,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_595,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_572,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | k9_eqrel_1(sK0,sK1,sK2) != X2
    | k3_filter_1(sK0,sK1,sK3) != X0
    | k8_eqrel_1(sK0,sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_573,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_466,plain,
    ( v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_467,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_27])).

cnf(c_470,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_1(sK3)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_470])).

cnf(c_552,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_13,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_480,plain,
    ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_481,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_483,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_27])).

cnf(c_484,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_538,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_484])).

cnf(c_539,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_541,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_12,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_495,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_27])).

cnf(c_498,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_498])).

cnf(c_526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_528,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1707,c_1708,c_1709,c_1704,c_1701,c_1698,c_1658,c_606,c_595,c_573,c_554,c_541,c_528,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:44:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.64/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.64/0.93  
% 1.64/0.93  ------  iProver source info
% 1.64/0.93  
% 1.64/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.64/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.64/0.93  git: non_committed_changes: false
% 1.64/0.93  git: last_make_outside_of_git: false
% 1.64/0.93  
% 1.64/0.93  ------ 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options
% 1.64/0.93  
% 1.64/0.93  --out_options                           all
% 1.64/0.93  --tptp_safe_out                         true
% 1.64/0.93  --problem_path                          ""
% 1.64/0.93  --include_path                          ""
% 1.64/0.93  --clausifier                            res/vclausify_rel
% 1.64/0.93  --clausifier_options                    --mode clausify
% 1.64/0.93  --stdin                                 false
% 1.64/0.93  --stats_out                             all
% 1.64/0.93  
% 1.64/0.93  ------ General Options
% 1.64/0.93  
% 1.64/0.93  --fof                                   false
% 1.64/0.93  --time_out_real                         305.
% 1.64/0.93  --time_out_virtual                      -1.
% 1.64/0.93  --symbol_type_check                     false
% 1.64/0.93  --clausify_out                          false
% 1.64/0.93  --sig_cnt_out                           false
% 1.64/0.93  --trig_cnt_out                          false
% 1.64/0.93  --trig_cnt_out_tolerance                1.
% 1.64/0.93  --trig_cnt_out_sk_spl                   false
% 1.64/0.93  --abstr_cl_out                          false
% 1.64/0.93  
% 1.64/0.93  ------ Global Options
% 1.64/0.93  
% 1.64/0.93  --schedule                              default
% 1.64/0.93  --add_important_lit                     false
% 1.64/0.93  --prop_solver_per_cl                    1000
% 1.64/0.93  --min_unsat_core                        false
% 1.64/0.93  --soft_assumptions                      false
% 1.64/0.93  --soft_lemma_size                       3
% 1.64/0.93  --prop_impl_unit_size                   0
% 1.64/0.93  --prop_impl_unit                        []
% 1.64/0.93  --share_sel_clauses                     true
% 1.64/0.93  --reset_solvers                         false
% 1.64/0.93  --bc_imp_inh                            [conj_cone]
% 1.64/0.93  --conj_cone_tolerance                   3.
% 1.64/0.93  --extra_neg_conj                        none
% 1.64/0.93  --large_theory_mode                     true
% 1.64/0.93  --prolific_symb_bound                   200
% 1.64/0.93  --lt_threshold                          2000
% 1.64/0.93  --clause_weak_htbl                      true
% 1.64/0.93  --gc_record_bc_elim                     false
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing Options
% 1.64/0.93  
% 1.64/0.93  --preprocessing_flag                    true
% 1.64/0.93  --time_out_prep_mult                    0.1
% 1.64/0.93  --splitting_mode                        input
% 1.64/0.93  --splitting_grd                         true
% 1.64/0.93  --splitting_cvd                         false
% 1.64/0.93  --splitting_cvd_svl                     false
% 1.64/0.93  --splitting_nvd                         32
% 1.64/0.93  --sub_typing                            true
% 1.64/0.93  --prep_gs_sim                           true
% 1.64/0.93  --prep_unflatten                        true
% 1.64/0.93  --prep_res_sim                          true
% 1.64/0.93  --prep_upred                            true
% 1.64/0.93  --prep_sem_filter                       exhaustive
% 1.64/0.93  --prep_sem_filter_out                   false
% 1.64/0.93  --pred_elim                             true
% 1.64/0.93  --res_sim_input                         true
% 1.64/0.93  --eq_ax_congr_red                       true
% 1.64/0.93  --pure_diseq_elim                       true
% 1.64/0.93  --brand_transform                       false
% 1.64/0.93  --non_eq_to_eq                          false
% 1.64/0.93  --prep_def_merge                        true
% 1.64/0.93  --prep_def_merge_prop_impl              false
% 1.64/0.93  --prep_def_merge_mbd                    true
% 1.64/0.93  --prep_def_merge_tr_red                 false
% 1.64/0.93  --prep_def_merge_tr_cl                  false
% 1.64/0.93  --smt_preprocessing                     true
% 1.64/0.93  --smt_ac_axioms                         fast
% 1.64/0.93  --preprocessed_out                      false
% 1.64/0.93  --preprocessed_stats                    false
% 1.64/0.93  
% 1.64/0.93  ------ Abstraction refinement Options
% 1.64/0.93  
% 1.64/0.93  --abstr_ref                             []
% 1.64/0.93  --abstr_ref_prep                        false
% 1.64/0.93  --abstr_ref_until_sat                   false
% 1.64/0.93  --abstr_ref_sig_restrict                funpre
% 1.64/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/0.93  --abstr_ref_under                       []
% 1.64/0.93  
% 1.64/0.93  ------ SAT Options
% 1.64/0.93  
% 1.64/0.93  --sat_mode                              false
% 1.64/0.93  --sat_fm_restart_options                ""
% 1.64/0.93  --sat_gr_def                            false
% 1.64/0.93  --sat_epr_types                         true
% 1.64/0.93  --sat_non_cyclic_types                  false
% 1.64/0.93  --sat_finite_models                     false
% 1.64/0.93  --sat_fm_lemmas                         false
% 1.64/0.93  --sat_fm_prep                           false
% 1.64/0.93  --sat_fm_uc_incr                        true
% 1.64/0.93  --sat_out_model                         small
% 1.64/0.93  --sat_out_clauses                       false
% 1.64/0.93  
% 1.64/0.93  ------ QBF Options
% 1.64/0.93  
% 1.64/0.93  --qbf_mode                              false
% 1.64/0.93  --qbf_elim_univ                         false
% 1.64/0.93  --qbf_dom_inst                          none
% 1.64/0.93  --qbf_dom_pre_inst                      false
% 1.64/0.93  --qbf_sk_in                             false
% 1.64/0.93  --qbf_pred_elim                         true
% 1.64/0.93  --qbf_split                             512
% 1.64/0.93  
% 1.64/0.93  ------ BMC1 Options
% 1.64/0.93  
% 1.64/0.93  --bmc1_incremental                      false
% 1.64/0.93  --bmc1_axioms                           reachable_all
% 1.64/0.93  --bmc1_min_bound                        0
% 1.64/0.93  --bmc1_max_bound                        -1
% 1.64/0.93  --bmc1_max_bound_default                -1
% 1.64/0.93  --bmc1_symbol_reachability              true
% 1.64/0.93  --bmc1_property_lemmas                  false
% 1.64/0.93  --bmc1_k_induction                      false
% 1.64/0.93  --bmc1_non_equiv_states                 false
% 1.64/0.93  --bmc1_deadlock                         false
% 1.64/0.93  --bmc1_ucm                              false
% 1.64/0.93  --bmc1_add_unsat_core                   none
% 1.64/0.93  --bmc1_unsat_core_children              false
% 1.64/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/0.93  --bmc1_out_stat                         full
% 1.64/0.93  --bmc1_ground_init                      false
% 1.64/0.93  --bmc1_pre_inst_next_state              false
% 1.64/0.93  --bmc1_pre_inst_state                   false
% 1.64/0.93  --bmc1_pre_inst_reach_state             false
% 1.64/0.93  --bmc1_out_unsat_core                   false
% 1.64/0.93  --bmc1_aig_witness_out                  false
% 1.64/0.93  --bmc1_verbose                          false
% 1.64/0.93  --bmc1_dump_clauses_tptp                false
% 1.64/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.64/0.93  --bmc1_dump_file                        -
% 1.64/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.64/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.64/0.93  --bmc1_ucm_extend_mode                  1
% 1.64/0.93  --bmc1_ucm_init_mode                    2
% 1.64/0.93  --bmc1_ucm_cone_mode                    none
% 1.64/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.64/0.93  --bmc1_ucm_relax_model                  4
% 1.64/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.64/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/0.93  --bmc1_ucm_layered_model                none
% 1.64/0.93  --bmc1_ucm_max_lemma_size               10
% 1.64/0.93  
% 1.64/0.93  ------ AIG Options
% 1.64/0.93  
% 1.64/0.93  --aig_mode                              false
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation Options
% 1.64/0.93  
% 1.64/0.93  --instantiation_flag                    true
% 1.64/0.93  --inst_sos_flag                         false
% 1.64/0.93  --inst_sos_phase                        true
% 1.64/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel_side                     num_symb
% 1.64/0.93  --inst_solver_per_active                1400
% 1.64/0.93  --inst_solver_calls_frac                1.
% 1.64/0.93  --inst_passive_queue_type               priority_queues
% 1.64/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/0.93  --inst_passive_queues_freq              [25;2]
% 1.64/0.93  --inst_dismatching                      true
% 1.64/0.93  --inst_eager_unprocessed_to_passive     true
% 1.64/0.93  --inst_prop_sim_given                   true
% 1.64/0.93  --inst_prop_sim_new                     false
% 1.64/0.93  --inst_subs_new                         false
% 1.64/0.93  --inst_eq_res_simp                      false
% 1.64/0.93  --inst_subs_given                       false
% 1.64/0.93  --inst_orphan_elimination               true
% 1.64/0.93  --inst_learning_loop_flag               true
% 1.64/0.93  --inst_learning_start                   3000
% 1.64/0.93  --inst_learning_factor                  2
% 1.64/0.93  --inst_start_prop_sim_after_learn       3
% 1.64/0.93  --inst_sel_renew                        solver
% 1.64/0.93  --inst_lit_activity_flag                true
% 1.64/0.93  --inst_restr_to_given                   false
% 1.64/0.93  --inst_activity_threshold               500
% 1.64/0.93  --inst_out_proof                        true
% 1.64/0.93  
% 1.64/0.93  ------ Resolution Options
% 1.64/0.93  
% 1.64/0.93  --resolution_flag                       true
% 1.64/0.93  --res_lit_sel                           adaptive
% 1.64/0.93  --res_lit_sel_side                      none
% 1.64/0.93  --res_ordering                          kbo
% 1.64/0.93  --res_to_prop_solver                    active
% 1.64/0.93  --res_prop_simpl_new                    false
% 1.64/0.93  --res_prop_simpl_given                  true
% 1.64/0.93  --res_passive_queue_type                priority_queues
% 1.64/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/0.93  --res_passive_queues_freq               [15;5]
% 1.64/0.93  --res_forward_subs                      full
% 1.64/0.93  --res_backward_subs                     full
% 1.64/0.93  --res_forward_subs_resolution           true
% 1.64/0.93  --res_backward_subs_resolution          true
% 1.64/0.93  --res_orphan_elimination                true
% 1.64/0.93  --res_time_limit                        2.
% 1.64/0.93  --res_out_proof                         true
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Options
% 1.64/0.93  
% 1.64/0.93  --superposition_flag                    true
% 1.64/0.93  --sup_passive_queue_type                priority_queues
% 1.64/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.64/0.93  --demod_completeness_check              fast
% 1.64/0.93  --demod_use_ground                      true
% 1.64/0.93  --sup_to_prop_solver                    passive
% 1.64/0.93  --sup_prop_simpl_new                    true
% 1.64/0.93  --sup_prop_simpl_given                  true
% 1.64/0.93  --sup_fun_splitting                     false
% 1.64/0.93  --sup_smt_interval                      50000
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Simplification Setup
% 1.64/0.93  
% 1.64/0.93  --sup_indices_passive                   []
% 1.64/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_full_bw                           [BwDemod]
% 1.64/0.93  --sup_immed_triv                        [TrivRules]
% 1.64/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_immed_bw_main                     []
% 1.64/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  
% 1.64/0.93  ------ Combination Options
% 1.64/0.93  
% 1.64/0.93  --comb_res_mult                         3
% 1.64/0.93  --comb_sup_mult                         2
% 1.64/0.93  --comb_inst_mult                        10
% 1.64/0.93  
% 1.64/0.93  ------ Debug Options
% 1.64/0.93  
% 1.64/0.93  --dbg_backtrace                         false
% 1.64/0.93  --dbg_dump_prop_clauses                 false
% 1.64/0.93  --dbg_dump_prop_clauses_file            -
% 1.64/0.93  --dbg_out_stat                          false
% 1.64/0.93  ------ Parsing...
% 1.64/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.64/0.93  ------ Proving...
% 1.64/0.93  ------ Problem Properties 
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  clauses                                 21
% 1.64/0.93  conjectures                             3
% 1.64/0.93  EPR                                     5
% 1.64/0.93  Horn                                    20
% 1.64/0.93  unary                                   11
% 1.64/0.93  binary                                  0
% 1.64/0.93  lits                                    47
% 1.64/0.93  lits eq                                 4
% 1.64/0.93  fd_pure                                 0
% 1.64/0.93  fd_pseudo                               0
% 1.64/0.93  fd_cond                                 0
% 1.64/0.93  fd_pseudo_cond                          0
% 1.64/0.93  AC symbols                              0
% 1.64/0.93  
% 1.64/0.93  ------ Schedule dynamic 5 is on 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  ------ 
% 1.64/0.93  Current options:
% 1.64/0.93  ------ 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options
% 1.64/0.93  
% 1.64/0.93  --out_options                           all
% 1.64/0.93  --tptp_safe_out                         true
% 1.64/0.93  --problem_path                          ""
% 1.64/0.93  --include_path                          ""
% 1.64/0.93  --clausifier                            res/vclausify_rel
% 1.64/0.93  --clausifier_options                    --mode clausify
% 1.64/0.93  --stdin                                 false
% 1.64/0.93  --stats_out                             all
% 1.64/0.93  
% 1.64/0.93  ------ General Options
% 1.64/0.93  
% 1.64/0.93  --fof                                   false
% 1.64/0.93  --time_out_real                         305.
% 1.64/0.93  --time_out_virtual                      -1.
% 1.64/0.93  --symbol_type_check                     false
% 1.64/0.93  --clausify_out                          false
% 1.64/0.93  --sig_cnt_out                           false
% 1.64/0.93  --trig_cnt_out                          false
% 1.64/0.93  --trig_cnt_out_tolerance                1.
% 1.64/0.93  --trig_cnt_out_sk_spl                   false
% 1.64/0.93  --abstr_cl_out                          false
% 1.64/0.93  
% 1.64/0.93  ------ Global Options
% 1.64/0.93  
% 1.64/0.93  --schedule                              default
% 1.64/0.93  --add_important_lit                     false
% 1.64/0.93  --prop_solver_per_cl                    1000
% 1.64/0.93  --min_unsat_core                        false
% 1.64/0.93  --soft_assumptions                      false
% 1.64/0.93  --soft_lemma_size                       3
% 1.64/0.93  --prop_impl_unit_size                   0
% 1.64/0.93  --prop_impl_unit                        []
% 1.64/0.93  --share_sel_clauses                     true
% 1.64/0.93  --reset_solvers                         false
% 1.64/0.93  --bc_imp_inh                            [conj_cone]
% 1.64/0.93  --conj_cone_tolerance                   3.
% 1.64/0.93  --extra_neg_conj                        none
% 1.64/0.93  --large_theory_mode                     true
% 1.64/0.93  --prolific_symb_bound                   200
% 1.64/0.93  --lt_threshold                          2000
% 1.64/0.93  --clause_weak_htbl                      true
% 1.64/0.93  --gc_record_bc_elim                     false
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing Options
% 1.64/0.93  
% 1.64/0.93  --preprocessing_flag                    true
% 1.64/0.93  --time_out_prep_mult                    0.1
% 1.64/0.93  --splitting_mode                        input
% 1.64/0.93  --splitting_grd                         true
% 1.64/0.93  --splitting_cvd                         false
% 1.64/0.93  --splitting_cvd_svl                     false
% 1.64/0.93  --splitting_nvd                         32
% 1.64/0.93  --sub_typing                            true
% 1.64/0.93  --prep_gs_sim                           true
% 1.64/0.93  --prep_unflatten                        true
% 1.64/0.93  --prep_res_sim                          true
% 1.64/0.93  --prep_upred                            true
% 1.64/0.93  --prep_sem_filter                       exhaustive
% 1.64/0.93  --prep_sem_filter_out                   false
% 1.64/0.93  --pred_elim                             true
% 1.64/0.93  --res_sim_input                         true
% 1.64/0.93  --eq_ax_congr_red                       true
% 1.64/0.93  --pure_diseq_elim                       true
% 1.64/0.93  --brand_transform                       false
% 1.64/0.93  --non_eq_to_eq                          false
% 1.64/0.93  --prep_def_merge                        true
% 1.64/0.93  --prep_def_merge_prop_impl              false
% 1.64/0.93  --prep_def_merge_mbd                    true
% 1.64/0.93  --prep_def_merge_tr_red                 false
% 1.64/0.93  --prep_def_merge_tr_cl                  false
% 1.64/0.93  --smt_preprocessing                     true
% 1.64/0.93  --smt_ac_axioms                         fast
% 1.64/0.93  --preprocessed_out                      false
% 1.64/0.93  --preprocessed_stats                    false
% 1.64/0.93  
% 1.64/0.93  ------ Abstraction refinement Options
% 1.64/0.93  
% 1.64/0.93  --abstr_ref                             []
% 1.64/0.93  --abstr_ref_prep                        false
% 1.64/0.93  --abstr_ref_until_sat                   false
% 1.64/0.93  --abstr_ref_sig_restrict                funpre
% 1.64/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/0.93  --abstr_ref_under                       []
% 1.64/0.93  
% 1.64/0.93  ------ SAT Options
% 1.64/0.93  
% 1.64/0.93  --sat_mode                              false
% 1.64/0.93  --sat_fm_restart_options                ""
% 1.64/0.93  --sat_gr_def                            false
% 1.64/0.93  --sat_epr_types                         true
% 1.64/0.93  --sat_non_cyclic_types                  false
% 1.64/0.93  --sat_finite_models                     false
% 1.64/0.93  --sat_fm_lemmas                         false
% 1.64/0.93  --sat_fm_prep                           false
% 1.64/0.93  --sat_fm_uc_incr                        true
% 1.64/0.93  --sat_out_model                         small
% 1.64/0.93  --sat_out_clauses                       false
% 1.64/0.93  
% 1.64/0.93  ------ QBF Options
% 1.64/0.93  
% 1.64/0.93  --qbf_mode                              false
% 1.64/0.93  --qbf_elim_univ                         false
% 1.64/0.93  --qbf_dom_inst                          none
% 1.64/0.93  --qbf_dom_pre_inst                      false
% 1.64/0.93  --qbf_sk_in                             false
% 1.64/0.93  --qbf_pred_elim                         true
% 1.64/0.93  --qbf_split                             512
% 1.64/0.93  
% 1.64/0.93  ------ BMC1 Options
% 1.64/0.93  
% 1.64/0.93  --bmc1_incremental                      false
% 1.64/0.93  --bmc1_axioms                           reachable_all
% 1.64/0.93  --bmc1_min_bound                        0
% 1.64/0.93  --bmc1_max_bound                        -1
% 1.64/0.93  --bmc1_max_bound_default                -1
% 1.64/0.93  --bmc1_symbol_reachability              true
% 1.64/0.93  --bmc1_property_lemmas                  false
% 1.64/0.93  --bmc1_k_induction                      false
% 1.64/0.93  --bmc1_non_equiv_states                 false
% 1.64/0.93  --bmc1_deadlock                         false
% 1.64/0.93  --bmc1_ucm                              false
% 1.64/0.93  --bmc1_add_unsat_core                   none
% 1.64/0.93  --bmc1_unsat_core_children              false
% 1.64/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/0.93  --bmc1_out_stat                         full
% 1.64/0.93  --bmc1_ground_init                      false
% 1.64/0.93  --bmc1_pre_inst_next_state              false
% 1.64/0.93  --bmc1_pre_inst_state                   false
% 1.64/0.93  --bmc1_pre_inst_reach_state             false
% 1.64/0.93  --bmc1_out_unsat_core                   false
% 1.64/0.93  --bmc1_aig_witness_out                  false
% 1.64/0.93  --bmc1_verbose                          false
% 1.64/0.93  --bmc1_dump_clauses_tptp                false
% 1.64/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.64/0.93  --bmc1_dump_file                        -
% 1.64/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.64/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.64/0.93  --bmc1_ucm_extend_mode                  1
% 1.64/0.93  --bmc1_ucm_init_mode                    2
% 1.64/0.93  --bmc1_ucm_cone_mode                    none
% 1.64/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.64/0.93  --bmc1_ucm_relax_model                  4
% 1.64/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.64/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/0.93  --bmc1_ucm_layered_model                none
% 1.64/0.93  --bmc1_ucm_max_lemma_size               10
% 1.64/0.93  
% 1.64/0.93  ------ AIG Options
% 1.64/0.93  
% 1.64/0.93  --aig_mode                              false
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation Options
% 1.64/0.93  
% 1.64/0.93  --instantiation_flag                    true
% 1.64/0.93  --inst_sos_flag                         false
% 1.64/0.93  --inst_sos_phase                        true
% 1.64/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel_side                     none
% 1.64/0.93  --inst_solver_per_active                1400
% 1.64/0.93  --inst_solver_calls_frac                1.
% 1.64/0.93  --inst_passive_queue_type               priority_queues
% 1.64/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/0.93  --inst_passive_queues_freq              [25;2]
% 1.64/0.93  --inst_dismatching                      true
% 1.64/0.93  --inst_eager_unprocessed_to_passive     true
% 1.64/0.93  --inst_prop_sim_given                   true
% 1.64/0.93  --inst_prop_sim_new                     false
% 1.64/0.93  --inst_subs_new                         false
% 1.64/0.93  --inst_eq_res_simp                      false
% 1.64/0.93  --inst_subs_given                       false
% 1.64/0.93  --inst_orphan_elimination               true
% 1.64/0.93  --inst_learning_loop_flag               true
% 1.64/0.93  --inst_learning_start                   3000
% 1.64/0.93  --inst_learning_factor                  2
% 1.64/0.93  --inst_start_prop_sim_after_learn       3
% 1.64/0.93  --inst_sel_renew                        solver
% 1.64/0.93  --inst_lit_activity_flag                true
% 1.64/0.93  --inst_restr_to_given                   false
% 1.64/0.93  --inst_activity_threshold               500
% 1.64/0.93  --inst_out_proof                        true
% 1.64/0.93  
% 1.64/0.93  ------ Resolution Options
% 1.64/0.93  
% 1.64/0.93  --resolution_flag                       false
% 1.64/0.93  --res_lit_sel                           adaptive
% 1.64/0.93  --res_lit_sel_side                      none
% 1.64/0.93  --res_ordering                          kbo
% 1.64/0.93  --res_to_prop_solver                    active
% 1.64/0.93  --res_prop_simpl_new                    false
% 1.64/0.93  --res_prop_simpl_given                  true
% 1.64/0.93  --res_passive_queue_type                priority_queues
% 1.64/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/0.93  --res_passive_queues_freq               [15;5]
% 1.64/0.93  --res_forward_subs                      full
% 1.64/0.93  --res_backward_subs                     full
% 1.64/0.93  --res_forward_subs_resolution           true
% 1.64/0.93  --res_backward_subs_resolution          true
% 1.64/0.93  --res_orphan_elimination                true
% 1.64/0.93  --res_time_limit                        2.
% 1.64/0.93  --res_out_proof                         true
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Options
% 1.64/0.93  
% 1.64/0.93  --superposition_flag                    true
% 1.64/0.93  --sup_passive_queue_type                priority_queues
% 1.64/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.64/0.93  --demod_completeness_check              fast
% 1.64/0.93  --demod_use_ground                      true
% 1.64/0.93  --sup_to_prop_solver                    passive
% 1.64/0.93  --sup_prop_simpl_new                    true
% 1.64/0.93  --sup_prop_simpl_given                  true
% 1.64/0.93  --sup_fun_splitting                     false
% 1.64/0.93  --sup_smt_interval                      50000
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Simplification Setup
% 1.64/0.93  
% 1.64/0.93  --sup_indices_passive                   []
% 1.64/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_full_bw                           [BwDemod]
% 1.64/0.93  --sup_immed_triv                        [TrivRules]
% 1.64/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_immed_bw_main                     []
% 1.64/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  
% 1.64/0.93  ------ Combination Options
% 1.64/0.93  
% 1.64/0.93  --comb_res_mult                         3
% 1.64/0.93  --comb_sup_mult                         2
% 1.64/0.93  --comb_inst_mult                        10
% 1.64/0.93  
% 1.64/0.93  ------ Debug Options
% 1.64/0.93  
% 1.64/0.93  --dbg_backtrace                         false
% 1.64/0.93  --dbg_dump_prop_clauses                 false
% 1.64/0.93  --dbg_dump_prop_clauses_file            -
% 1.64/0.93  --dbg_out_stat                          false
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  ------ Proving...
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  % SZS status Theorem for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  fof(f13,conjecture,(
% 1.64/0.93    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f14,negated_conjecture,(
% 1.64/0.93    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.64/0.93    inference(negated_conjecture,[],[f13])).
% 1.64/0.93  
% 1.64/0.93  fof(f37,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f14])).
% 1.64/0.93  
% 1.64/0.93  fof(f38,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f37])).
% 1.64/0.93  
% 1.64/0.93  fof(f45,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) => (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3)) & r3_binop_1(X0,X2,sK3) & m2_filter_1(sK3,X0,X1))) )),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f44,plain,(
% 1.64/0.93    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,sK2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(sK2,X0))) )),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f43,plain,(
% 1.64/0.93    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,sK1)) & m1_subset_1(X2,X0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,X0))) )),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f42,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f46,plain,(
% 1.64/0.93    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.64/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f45,f44,f43,f42])).
% 1.64/0.93  
% 1.64/0.93  fof(f67,plain,(
% 1.64/0.93    v1_partfun1(sK1,sK0)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f5,axiom,(
% 1.64/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f21,plain,(
% 1.64/0.93    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f5])).
% 1.64/0.93  
% 1.64/0.93  fof(f22,plain,(
% 1.64/0.93    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f21])).
% 1.64/0.93  
% 1.64/0.93  fof(f54,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_funct_1(k3_filter_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f22])).
% 1.64/0.93  
% 1.64/0.93  fof(f69,plain,(
% 1.64/0.93    v8_relat_2(sK1)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f68,plain,(
% 1.64/0.93    v3_relat_2(sK1)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f66,plain,(
% 1.64/0.93    ~v1_xboole_0(sK0)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f70,plain,(
% 1.64/0.93    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f55,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f22])).
% 1.64/0.93  
% 1.64/0.93  fof(f56,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f22])).
% 1.64/0.93  
% 1.64/0.93  fof(f11,axiom,(
% 1.64/0.93    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f33,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f11])).
% 1.64/0.93  
% 1.64/0.93  fof(f34,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f33])).
% 1.64/0.93  
% 1.64/0.93  fof(f64,plain,(
% 1.64/0.93    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f34])).
% 1.64/0.93  
% 1.64/0.93  fof(f72,plain,(
% 1.64/0.93    m2_filter_1(sK3,sK0,sK1)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f12,axiom,(
% 1.64/0.93    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f35,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f12])).
% 1.64/0.93  
% 1.64/0.93  fof(f36,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f35])).
% 1.64/0.93  
% 1.64/0.93  fof(f65,plain,(
% 1.64/0.93    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f36])).
% 1.64/0.93  
% 1.64/0.93  fof(f3,axiom,(
% 1.64/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f17,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f3])).
% 1.64/0.93  
% 1.64/0.93  fof(f18,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f17])).
% 1.64/0.93  
% 1.64/0.93  fof(f39,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.64/0.93    inference(nnf_transformation,[],[f18])).
% 1.64/0.93  
% 1.64/0.93  fof(f49,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f39])).
% 1.64/0.93  
% 1.64/0.93  fof(f7,axiom,(
% 1.64/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f25,plain,(
% 1.64/0.93    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f7])).
% 1.64/0.93  
% 1.64/0.93  fof(f26,plain,(
% 1.64/0.93    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f25])).
% 1.64/0.93  
% 1.64/0.93  fof(f58,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f26])).
% 1.64/0.93  
% 1.64/0.93  fof(f1,axiom,(
% 1.64/0.93    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f15,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f1])).
% 1.64/0.93  
% 1.64/0.93  fof(f47,plain,(
% 1.64/0.93    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f15])).
% 1.64/0.93  
% 1.64/0.93  fof(f9,axiom,(
% 1.64/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f29,plain,(
% 1.64/0.93    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f9])).
% 1.64/0.93  
% 1.64/0.93  fof(f30,plain,(
% 1.64/0.93    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f29])).
% 1.64/0.93  
% 1.64/0.93  fof(f62,plain,(
% 1.64/0.93    ( ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f30])).
% 1.64/0.93  
% 1.64/0.93  fof(f10,axiom,(
% 1.64/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f31,plain,(
% 1.64/0.93    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.64/0.93    inference(ennf_transformation,[],[f10])).
% 1.64/0.93  
% 1.64/0.93  fof(f32,plain,(
% 1.64/0.93    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.64/0.93    inference(flattening,[],[f31])).
% 1.64/0.93  
% 1.64/0.93  fof(f63,plain,(
% 1.64/0.93    ( ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f32])).
% 1.64/0.93  
% 1.64/0.93  fof(f6,axiom,(
% 1.64/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f23,plain,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.64/0.93    inference(ennf_transformation,[],[f6])).
% 1.64/0.93  
% 1.64/0.93  fof(f24,plain,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.64/0.93    inference(flattening,[],[f23])).
% 1.64/0.93  
% 1.64/0.93  fof(f57,plain,(
% 1.64/0.93    ( ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f24])).
% 1.64/0.93  
% 1.64/0.93  fof(f4,axiom,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f19,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f4])).
% 1.64/0.93  
% 1.64/0.93  fof(f20,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.64/0.93    inference(flattening,[],[f19])).
% 1.64/0.93  
% 1.64/0.93  fof(f40,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.64/0.93    inference(nnf_transformation,[],[f20])).
% 1.64/0.93  
% 1.64/0.93  fof(f41,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.64/0.93    inference(flattening,[],[f40])).
% 1.64/0.93  
% 1.64/0.93  fof(f52,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f41])).
% 1.64/0.93  
% 1.64/0.93  fof(f73,plain,(
% 1.64/0.93    r3_binop_1(sK0,sK2,sK3)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f51,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f41])).
% 1.64/0.93  
% 1.64/0.93  fof(f53,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f41])).
% 1.64/0.93  
% 1.64/0.93  fof(f74,plain,(
% 1.64/0.93    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  fof(f2,axiom,(
% 1.64/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f16,plain,(
% 1.64/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.93    inference(ennf_transformation,[],[f2])).
% 1.64/0.93  
% 1.64/0.93  fof(f48,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.93    inference(cnf_transformation,[],[f16])).
% 1.64/0.93  
% 1.64/0.93  fof(f8,axiom,(
% 1.64/0.93    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 1.64/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f27,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f8])).
% 1.64/0.93  
% 1.64/0.93  fof(f28,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 1.64/0.93    inference(flattening,[],[f27])).
% 1.64/0.93  
% 1.64/0.93  fof(f59,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f28])).
% 1.64/0.93  
% 1.64/0.93  fof(f60,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f28])).
% 1.64/0.93  
% 1.64/0.93  fof(f61,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f28])).
% 1.64/0.93  
% 1.64/0.93  fof(f71,plain,(
% 1.64/0.93    m1_subset_1(sK2,sK0)),
% 1.64/0.93    inference(cnf_transformation,[],[f46])).
% 1.64/0.93  
% 1.64/0.93  cnf(c_26,negated_conjecture,
% 1.64/0.93      ( v1_partfun1(sK1,sK0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f67]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_9,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v8_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f54]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_24,negated_conjecture,
% 1.64/0.93      ( v8_relat_2(sK1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f69]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_739,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != X2 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_740,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_739]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_25,negated_conjecture,
% 1.64/0.93      ( v3_relat_2(sK1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f68]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_744,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_740,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_745,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_744]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_985,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_745]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_986,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_985]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_27,negated_conjecture,
% 1.64/0.93      ( ~ v1_xboole_0(sK0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f66]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_23,negated_conjecture,
% 1.64/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/0.93      inference(cnf_transformation,[],[f70]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_990,plain,
% 1.64/0.93      ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_986,c_27,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_991,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_990]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1707,plain,
% 1.64/0.93      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ v1_funct_1(sK3) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_991]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_8,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v8_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f55]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_772,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != X2 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_773,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_772]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_777,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_773,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_778,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_777]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_961,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_778]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_962,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_961]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_966,plain,
% 1.64/0.93      ( ~ v1_funct_1(X0)
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_962,c_27,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_967,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_funct_1(X0) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_966]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1708,plain,
% 1.64/0.93      ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_funct_1(sK3) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_967]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_7,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v8_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f56]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_805,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != X2 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_806,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_805]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_810,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_806,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_811,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_partfun1(sK1,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_810]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_937,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_811]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_938,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_937]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_942,plain,
% 1.64/0.93      ( ~ v1_funct_1(X0)
% 1.64/0.93      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_938,c_27,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_943,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.64/0.93      | ~ v1_funct_1(X0) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_942]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1709,plain,
% 1.64/0.93      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.64/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_funct_1(sK3) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_943]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_17,plain,
% 1.64/0.93      ( ~ m2_filter_1(X0,X1,X2)
% 1.64/0.93      | ~ r1_binop_1(X1,X3,X0)
% 1.64/0.93      | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X3,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v8_relat_2(X2)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f64]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_21,negated_conjecture,
% 1.64/0.93      ( m2_filter_1(sK3,sK0,sK1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f72]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_445,plain,
% 1.64/0.93      ( ~ r1_binop_1(X0,X1,X2)
% 1.64/0.93      | r1_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.64/0.93      | ~ v1_partfun1(X3,X0)
% 1.64/0.93      | ~ m1_subset_1(X1,X0)
% 1.64/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(X3)
% 1.64/0.93      | ~ v8_relat_2(X3)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | sK3 != X2
% 1.64/0.93      | sK1 != X3
% 1.64/0.93      | sK0 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_446,plain,
% 1.64/0.93      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r1_binop_1(sK0,X0,sK3)
% 1.64/0.93      | ~ v1_partfun1(sK1,sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v8_relat_2(sK1)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_445]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_450,plain,
% 1.64/0.93      ( ~ r1_binop_1(sK0,X0,sK3)
% 1.64/0.93      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ m1_subset_1(X0,sK0) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_446,c_27,c_26,c_25,c_24,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_451,plain,
% 1.64/0.93      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r1_binop_1(sK0,X0,sK3)
% 1.64/0.93      | ~ m1_subset_1(X0,sK0) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_450]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1704,plain,
% 1.64/0.93      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r1_binop_1(sK0,sK2,sK3)
% 1.64/0.93      | ~ m1_subset_1(sK2,sK0) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_451]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_18,plain,
% 1.64/0.93      ( ~ m2_filter_1(X0,X1,X2)
% 1.64/0.93      | ~ r2_binop_1(X1,X3,X0)
% 1.64/0.93      | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.64/0.93      | ~ v1_partfun1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X3,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X2)
% 1.64/0.93      | ~ v8_relat_2(X2)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f65]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_424,plain,
% 1.64/0.93      ( ~ r2_binop_1(X0,X1,X2)
% 1.64/0.93      | r2_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.64/0.93      | ~ v1_partfun1(X3,X0)
% 1.64/0.93      | ~ m1_subset_1(X1,X0)
% 1.64/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(X3)
% 1.64/0.93      | ~ v8_relat_2(X3)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | sK3 != X2
% 1.64/0.93      | sK1 != X3
% 1.64/0.93      | sK0 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_425,plain,
% 1.64/0.93      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r2_binop_1(sK0,X0,sK3)
% 1.64/0.93      | ~ v1_partfun1(sK1,sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v8_relat_2(sK1)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_424]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_429,plain,
% 1.64/0.93      ( ~ r2_binop_1(sK0,X0,sK3)
% 1.64/0.93      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ m1_subset_1(X0,sK0) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_425,c_27,c_26,c_25,c_24,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_430,plain,
% 1.64/0.93      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r2_binop_1(sK0,X0,sK3)
% 1.64/0.93      | ~ m1_subset_1(X0,sK0) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_429]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1701,plain,
% 1.64/0.93      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r2_binop_1(sK0,sK2,sK3)
% 1.64/0.93      | ~ m1_subset_1(sK2,sK0) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_430]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_3,plain,
% 1.64/0.93      ( ~ m2_subset_1(X0,X1,X2)
% 1.64/0.93      | m1_subset_1(X0,X2)
% 1.64/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(X2) ),
% 1.64/0.93      inference(cnf_transformation,[],[f49]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_11,plain,
% 1.64/0.93      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
% 1.64/0.93      | ~ v1_partfun1(X1,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(X1)
% 1.64/0.93      | ~ v8_relat_2(X1)
% 1.64/0.93      | v1_xboole_0(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f58]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_376,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | m1_subset_1(X3,X4)
% 1.64/0.93      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X5)
% 1.64/0.93      | v1_xboole_0(X4)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | k9_eqrel_1(X1,X0,X2) != X3
% 1.64/0.93      | k8_eqrel_1(X1,X0) != X4
% 1.64/0.93      | k1_zfmisc_1(X1) != X5 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_377,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.64/0.93      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_376]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_0,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.64/0.93      | ~ v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f47]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_401,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X1,X0)) ),
% 1.64/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_377,c_0]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_640,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_401,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_641,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(X1,X0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_640]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_645,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.64/0.93      | ~ m1_subset_1(X1,X0)
% 1.64/0.93      | ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_641,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_646,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(X1,X0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_645]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_913,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,X1)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(X1,sK1),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(X1,sK1))
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_646]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_914,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_913]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_918,plain,
% 1.64/0.93      ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_914,c_27,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_919,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_918]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1157,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,sK0)
% 1.64/0.93      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ sP0_iProver_split ),
% 1.64/0.93      inference(splitting,
% 1.64/0.93                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.64/0.93                [c_919]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1698,plain,
% 1.64/0.93      ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(sK2,sK0)
% 1.64/0.93      | ~ sP0_iProver_split ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_1157]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1158,plain,
% 1.64/0.93      ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | sP0_iProver_split ),
% 1.64/0.93      inference(splitting,
% 1.64/0.93                [splitting(split),new_symbols(definition,[])],
% 1.64/0.93                [c_919]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1537,plain,
% 1.64/0.93      ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 1.64/0.93      | v1_xboole_0(k8_eqrel_1(sK0,sK1)) = iProver_top
% 1.64/0.93      | sP0_iProver_split = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_15,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
% 1.64/0.93      inference(cnf_transformation,[],[f62]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_694,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_695,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_694]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_699,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_695,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_700,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_699]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_894,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | v1_xboole_0(X0)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_700]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_895,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_894]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_697,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_695]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_897,plain,
% 1.64/0.93      ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_895,c_27,c_26,c_25,c_23,c_697]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1539,plain,
% 1.64/0.93      ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_16,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0)
% 1.64/0.93      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f63]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_673,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_674,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_673]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_678,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_674,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_679,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_678]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_905,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_679]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_906,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_905]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_676,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v3_relat_2(sK1)
% 1.64/0.93      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_674]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_908,plain,
% 1.64/0.93      ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_906,c_26,c_25,c_23,c_676]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1565,plain,
% 1.64/0.93      ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.64/0.93      inference(light_normalisation,[status(thm)],[c_1539,c_908]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_10,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | ~ v8_relat_2(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f57]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_718,plain,
% 1.64/0.93      ( ~ v1_partfun1(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.64/0.93      | ~ v3_relat_2(X0)
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_719,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | ~ v3_relat_2(sK1) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_718]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_723,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ v1_partfun1(sK1,X0) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_719,c_25]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_724,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,X0)
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_723]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_883,plain,
% 1.64/0.93      ( m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.64/0.93      | sK1 != sK1
% 1.64/0.93      | sK0 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_724]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_884,plain,
% 1.64/0.93      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_883]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_721,plain,
% 1.64/0.93      ( ~ v1_partfun1(sK1,sK0)
% 1.64/0.93      | m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | ~ v3_relat_2(sK1) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_719]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_886,plain,
% 1.64/0.93      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_884,c_26,c_25,c_23,c_721]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1540,plain,
% 1.64/0.93      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1572,plain,
% 1.64/0.93      ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.64/0.93      inference(light_normalisation,[status(thm)],[c_1540,c_908]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1586,plain,
% 1.64/0.93      ( sP0_iProver_split = iProver_top ),
% 1.64/0.93      inference(forward_subsumption_resolution,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1537,c_1565,c_1572]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1658,plain,
% 1.64/0.93      ( sP0_iProver_split ),
% 1.64/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_1586]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_5,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | r2_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ r3_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f52]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_20,negated_conjecture,
% 1.64/0.93      ( r3_binop_1(sK0,sK2,sK3) ),
% 1.64/0.93      inference(cnf_transformation,[],[f73]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_605,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | r2_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | sK3 != X0
% 1.64/0.93      | sK2 != X2
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_606,plain,
% 1.64/0.93      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | r2_binop_1(sK0,sK2,sK3)
% 1.64/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK2,sK0)
% 1.64/0.93      | ~ v1_funct_1(sK3) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_605]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_6,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | r1_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ r3_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f51]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_594,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | r1_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | sK3 != X0
% 1.64/0.93      | sK2 != X2
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_595,plain,
% 1.64/0.93      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | r1_binop_1(sK0,sK2,sK3)
% 1.64/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK2,sK0)
% 1.64/0.93      | ~ v1_funct_1(sK3) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_594]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_4,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ r1_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ r2_binop_1(X1,X2,X0)
% 1.64/0.93      | r3_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f53]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_19,negated_conjecture,
% 1.64/0.93      ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
% 1.64/0.93      inference(cnf_transformation,[],[f74]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_572,plain,
% 1.64/0.93      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ r1_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ r2_binop_1(X1,X2,X0)
% 1.64/0.93      | ~ m1_subset_1(X2,X1)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_funct_1(X0)
% 1.64/0.93      | k9_eqrel_1(sK0,sK1,sK2) != X2
% 1.64/0.93      | k3_filter_1(sK0,sK1,sK3) != X0
% 1.64/0.93      | k8_eqrel_1(sK0,sK1) != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_573,plain,
% 1.64/0.93      ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.64/0.93      | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.64/0.93      | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.64/0.93      | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_572]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/0.93      | v1_relat_1(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f48]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_14,plain,
% 1.64/0.93      ( ~ m2_filter_1(X0,X1,X2)
% 1.64/0.93      | v1_funct_1(X0)
% 1.64/0.93      | ~ v1_relat_1(X2)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f59]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_466,plain,
% 1.64/0.93      ( v1_funct_1(X0)
% 1.64/0.93      | ~ v1_relat_1(X1)
% 1.64/0.93      | v1_xboole_0(X2)
% 1.64/0.93      | sK3 != X0
% 1.64/0.93      | sK1 != X1
% 1.64/0.93      | sK0 != X2 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_467,plain,
% 1.64/0.93      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_466]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_469,plain,
% 1.64/0.93      ( ~ v1_relat_1(sK1) | v1_funct_1(sK3) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_467,c_27]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_470,plain,
% 1.64/0.93      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_469]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_551,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/0.93      | v1_funct_1(sK3)
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_470]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_552,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.64/0.93      | v1_funct_1(sK3) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_551]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_554,plain,
% 1.64/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.64/0.93      | v1_funct_1(sK3) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_552]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_13,plain,
% 1.64/0.93      ( ~ m2_filter_1(X0,X1,X2)
% 1.64/0.93      | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_relat_1(X2)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f60]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_480,plain,
% 1.64/0.93      ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.64/0.93      | ~ v1_relat_1(X2)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK3 != X0
% 1.64/0.93      | sK1 != X2
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_481,plain,
% 1.64/0.93      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ v1_relat_1(sK1)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_480]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_483,plain,
% 1.64/0.93      ( ~ v1_relat_1(sK1) | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_481,c_27]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_484,plain,
% 1.64/0.93      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~ v1_relat_1(sK1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_483]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_538,plain,
% 1.64/0.93      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_484]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_539,plain,
% 1.64/0.93      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_538]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_541,plain,
% 1.64/0.93      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_539]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_12,plain,
% 1.64/0.93      ( ~ m2_filter_1(X0,X1,X2)
% 1.64/0.93      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_relat_1(X2)
% 1.64/0.93      | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f61]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_494,plain,
% 1.64/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.64/0.93      | ~ v1_relat_1(X2)
% 1.64/0.93      | v1_xboole_0(X1)
% 1.64/0.93      | sK3 != X0
% 1.64/0.93      | sK1 != X2
% 1.64/0.93      | sK0 != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_495,plain,
% 1.64/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_relat_1(sK1)
% 1.64/0.93      | v1_xboole_0(sK0) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_494]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_497,plain,
% 1.64/0.93      ( ~ v1_relat_1(sK1)
% 1.64/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_495,c_27]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_498,plain,
% 1.64/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ v1_relat_1(sK1) ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_497]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_525,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | sK1 != X0 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_498]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_526,plain,
% 1.64/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_525]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_528,plain,
% 1.64/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.64/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_526]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_22,negated_conjecture,
% 1.64/0.93      ( m1_subset_1(sK2,sK0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f71]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(contradiction,plain,
% 1.64/0.93      ( $false ),
% 1.64/0.93      inference(minisat,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1707,c_1708,c_1709,c_1704,c_1701,c_1698,c_1658,c_606,
% 1.64/0.93                 c_595,c_573,c_554,c_541,c_528,c_22,c_23]) ).
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  ------                               Statistics
% 1.64/0.93  
% 1.64/0.93  ------ General
% 1.64/0.93  
% 1.64/0.93  abstr_ref_over_cycles:                  0
% 1.64/0.93  abstr_ref_under_cycles:                 0
% 1.64/0.93  gc_basic_clause_elim:                   0
% 1.64/0.93  forced_gc_time:                         0
% 1.64/0.93  parsing_time:                           0.008
% 1.64/0.93  unif_index_cands_time:                  0.
% 1.64/0.93  unif_index_add_time:                    0.
% 1.64/0.93  orderings_time:                         0.
% 1.64/0.93  out_proof_time:                         0.018
% 1.64/0.93  total_time:                             0.074
% 1.64/0.93  num_of_symbols:                         55
% 1.64/0.93  num_of_terms:                           1031
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing
% 1.64/0.93  
% 1.64/0.93  num_of_splits:                          1
% 1.64/0.93  num_of_split_atoms:                     1
% 1.64/0.93  num_of_reused_defs:                     0
% 1.64/0.93  num_eq_ax_congr_red:                    3
% 1.64/0.93  num_of_sem_filtered_clauses:            1
% 1.64/0.93  num_of_subtypes:                        1
% 1.64/0.93  monotx_restored_types:                  0
% 1.64/0.93  sat_num_of_epr_types:                   0
% 1.64/0.93  sat_num_of_non_cyclic_types:            0
% 1.64/0.93  sat_guarded_non_collapsed_types:        0
% 1.64/0.93  num_pure_diseq_elim:                    0
% 1.64/0.93  simp_replaced_by:                       0
% 1.64/0.93  res_preprocessed:                       119
% 1.64/0.93  prep_upred:                             0
% 1.64/0.93  prep_unflattend:                        47
% 1.64/0.93  smt_new_axioms:                         0
% 1.64/0.93  pred_elim_cands:                        6
% 1.64/0.93  pred_elim:                              7
% 1.64/0.93  pred_elim_cl:                           8
% 1.64/0.93  pred_elim_cycles:                       10
% 1.64/0.93  merged_defs:                            0
% 1.64/0.93  merged_defs_ncl:                        0
% 1.64/0.93  bin_hyper_res:                          0
% 1.64/0.93  prep_cycles:                            4
% 1.64/0.93  pred_elim_time:                         0.01
% 1.64/0.93  splitting_time:                         0.
% 1.64/0.93  sem_filter_time:                        0.
% 1.64/0.93  monotx_time:                            0.
% 1.64/0.93  subtype_inf_time:                       0.
% 1.64/0.93  
% 1.64/0.93  ------ Problem properties
% 1.64/0.93  
% 1.64/0.93  clauses:                                21
% 1.64/0.93  conjectures:                            3
% 1.64/0.93  epr:                                    5
% 1.64/0.93  horn:                                   20
% 1.64/0.93  ground:                                 14
% 1.64/0.93  unary:                                  11
% 1.64/0.93  binary:                                 0
% 1.64/0.93  lits:                                   47
% 1.64/0.93  lits_eq:                                4
% 1.64/0.93  fd_pure:                                0
% 1.64/0.93  fd_pseudo:                              0
% 1.64/0.93  fd_cond:                                0
% 1.64/0.93  fd_pseudo_cond:                         0
% 1.64/0.93  ac_symbols:                             0
% 1.64/0.93  
% 1.64/0.93  ------ Propositional Solver
% 1.64/0.93  
% 1.64/0.93  prop_solver_calls:                      22
% 1.64/0.93  prop_fast_solver_calls:                 942
% 1.64/0.93  smt_solver_calls:                       0
% 1.64/0.93  smt_fast_solver_calls:                  0
% 1.64/0.93  prop_num_of_clauses:                    323
% 1.64/0.93  prop_preprocess_simplified:             2666
% 1.64/0.93  prop_fo_subsumed:                       43
% 1.64/0.93  prop_solver_time:                       0.
% 1.64/0.93  smt_solver_time:                        0.
% 1.64/0.93  smt_fast_solver_time:                   0.
% 1.64/0.93  prop_fast_solver_time:                  0.
% 1.64/0.93  prop_unsat_core_time:                   0.
% 1.64/0.93  
% 1.64/0.93  ------ QBF
% 1.64/0.93  
% 1.64/0.93  qbf_q_res:                              0
% 1.64/0.93  qbf_num_tautologies:                    0
% 1.64/0.93  qbf_prep_cycles:                        0
% 1.64/0.93  
% 1.64/0.93  ------ BMC1
% 1.64/0.93  
% 1.64/0.93  bmc1_current_bound:                     -1
% 1.64/0.93  bmc1_last_solved_bound:                 -1
% 1.64/0.93  bmc1_unsat_core_size:                   -1
% 1.64/0.93  bmc1_unsat_core_parents_size:           -1
% 1.64/0.93  bmc1_merge_next_fun:                    0
% 1.64/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation
% 1.64/0.93  
% 1.64/0.93  inst_num_of_clauses:                    40
% 1.64/0.93  inst_num_in_passive:                    15
% 1.64/0.93  inst_num_in_active:                     19
% 1.64/0.93  inst_num_in_unprocessed:                5
% 1.64/0.93  inst_num_of_loops:                      20
% 1.64/0.93  inst_num_of_learning_restarts:          0
% 1.64/0.93  inst_num_moves_active_passive:          0
% 1.64/0.93  inst_lit_activity:                      0
% 1.64/0.93  inst_lit_activity_moves:                0
% 1.64/0.93  inst_num_tautologies:                   0
% 1.64/0.93  inst_num_prop_implied:                  0
% 1.64/0.93  inst_num_existing_simplified:           0
% 1.64/0.93  inst_num_eq_res_simplified:             0
% 1.64/0.93  inst_num_child_elim:                    0
% 1.64/0.93  inst_num_of_dismatching_blockings:      0
% 1.64/0.93  inst_num_of_non_proper_insts:           4
% 1.64/0.93  inst_num_of_duplicates:                 0
% 1.64/0.93  inst_inst_num_from_inst_to_res:         0
% 1.64/0.93  inst_dismatching_checking_time:         0.
% 1.64/0.93  
% 1.64/0.93  ------ Resolution
% 1.64/0.93  
% 1.64/0.93  res_num_of_clauses:                     0
% 1.64/0.93  res_num_in_passive:                     0
% 1.64/0.93  res_num_in_active:                      0
% 1.64/0.93  res_num_of_loops:                       123
% 1.64/0.93  res_forward_subset_subsumed:            0
% 1.64/0.93  res_backward_subset_subsumed:           0
% 1.64/0.93  res_forward_subsumed:                   0
% 1.64/0.93  res_backward_subsumed:                  0
% 1.64/0.93  res_forward_subsumption_resolution:     1
% 1.64/0.93  res_backward_subsumption_resolution:    0
% 1.64/0.93  res_clause_to_clause_subsumption:       32
% 1.64/0.93  res_orphan_elimination:                 0
% 1.64/0.93  res_tautology_del:                      3
% 1.64/0.93  res_num_eq_res_simplified:              0
% 1.64/0.93  res_num_sel_changes:                    0
% 1.64/0.93  res_moves_from_active_to_pass:          0
% 1.64/0.93  
% 1.64/0.93  ------ Superposition
% 1.64/0.93  
% 1.64/0.93  sup_time_total:                         0.
% 1.64/0.93  sup_time_generating:                    0.
% 1.64/0.93  sup_time_sim_full:                      0.
% 1.64/0.93  sup_time_sim_immed:                     0.
% 1.64/0.93  
% 1.64/0.93  sup_num_of_clauses:                     21
% 1.64/0.93  sup_num_in_active:                      2
% 1.64/0.93  sup_num_in_passive:                     19
% 1.64/0.93  sup_num_of_loops:                       2
% 1.64/0.93  sup_fw_superposition:                   0
% 1.64/0.93  sup_bw_superposition:                   0
% 1.64/0.93  sup_immediate_simplified:               0
% 1.64/0.93  sup_given_eliminated:                   0
% 1.64/0.93  comparisons_done:                       0
% 1.64/0.93  comparisons_avoided:                    0
% 1.64/0.93  
% 1.64/0.93  ------ Simplifications
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  sim_fw_subset_subsumed:                 0
% 1.64/0.93  sim_bw_subset_subsumed:                 0
% 1.64/0.93  sim_fw_subsumed:                        0
% 1.64/0.93  sim_bw_subsumed:                        0
% 1.64/0.93  sim_fw_subsumption_res:                 3
% 1.64/0.93  sim_bw_subsumption_res:                 0
% 1.64/0.93  sim_tautology_del:                      0
% 1.64/0.93  sim_eq_tautology_del:                   0
% 1.64/0.93  sim_eq_res_simp:                        0
% 1.64/0.93  sim_fw_demodulated:                     0
% 1.64/0.93  sim_bw_demodulated:                     0
% 1.64/0.93  sim_light_normalised:                   2
% 1.64/0.93  sim_joinable_taut:                      0
% 1.64/0.93  sim_joinable_simp:                      0
% 1.64/0.93  sim_ac_normalised:                      0
% 1.64/0.93  sim_smt_subsumption:                    0
% 1.64/0.93  
%------------------------------------------------------------------------------
