%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:56 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  207 (1127 expanded)
%              Number of clauses        :  132 ( 236 expanded)
%              Number of leaves         :   18 ( 417 expanded)
%              Depth                    :   21
%              Number of atoms          : 1094 (8935 expanded)
%              Number of equality atoms :   69 ( 109 expanded)
%              Maximal formula depth    :   14 (   6 average)
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r3_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f46,f45,f44,f43])).

fof(f69,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f71,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f34])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f36])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f41])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_27,negated_conjecture,
    ( v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
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

cnf(c_25,negated_conjecture,
    ( v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_661,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_662,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_26,negated_conjecture,
    ( v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_666,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_26])).

cnf(c_667,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_907,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK1,X0))
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_667])).

cnf(c_908,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_912,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_28,c_24])).

cnf(c_913,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
    inference(renaming,[status(thm)],[c_912])).

cnf(c_1834,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_9,plain,
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

cnf(c_694,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_695,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_26])).

cnf(c_700,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_883,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_700])).

cnf(c_884,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_888,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_884,c_28,c_24])).

cnf(c_889,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_888])).

cnf(c_1835,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_8,plain,
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

cnf(c_727,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v3_relat_2(X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_728,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK1,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_26])).

cnf(c_733,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_859,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_733])).

cnf(c_860,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_864,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_28,c_24])).

cnf(c_865,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_864])).

cnf(c_1836,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1807,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1730])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_388,plain,
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

cnf(c_389,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_393,plain,
    ( ~ r1_binop_1(sK0,X0,sK3)
    | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_28,c_27,c_26,c_25,c_24])).

cnf(c_394,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_1724,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_394])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_367,plain,
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

cnf(c_368,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
    ( ~ r2_binop_1(sK0,X0,sK3)
    | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_28,c_27,c_26,c_25,c_24])).

cnf(c_373,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,X0,sK3)
    | ~ m1_subset_1(X0,sK0) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_1721,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_4,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_319,plain,
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
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_320,plain,
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
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_344,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_320,c_0])).

cnf(c_562,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_25])).

cnf(c_563,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_567,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_26])).

cnf(c_568,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
    inference(renaming,[status(thm)],[c_567])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
    | ~ m1_subset_1(k8_eqrel_1(X1,sK1),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(k8_eqrel_1(X1,sK1))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_568])).

cnf(c_836,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_840,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_28,c_24])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_840])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(X0,sK0)
    | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_841])).

cnf(c_1718,plain,
    ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK2,sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1096,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_841])).

cnf(c_1524,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_616,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_617,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_621,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_26])).

cnf(c_622,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
    inference(renaming,[status(thm)],[c_621])).

cnf(c_816,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_622])).

cnf(c_817,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_619,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_819,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_28,c_27,c_26,c_24,c_619])).

cnf(c_1526,plain,
    ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_595,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_596,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK1,X0)
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_26])).

cnf(c_601,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_827,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_601])).

cnf(c_828,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_598,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1)
    | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_830,plain,
    ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_27,c_26,c_24,c_598])).

cnf(c_1550,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1526,c_830])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_640,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_641,plain,
    ( ~ v1_partfun1(sK1,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK1) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_645,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ v1_partfun1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_26])).

cnf(c_646,plain,
    ( ~ v1_partfun1(sK1,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_805,plain,
    ( m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_646])).

cnf(c_806,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_643,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_808,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_27,c_26,c_24,c_643])).

cnf(c_1527,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1555,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1527,c_830])).

cnf(c_1585,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1524,c_1550,c_1555])).

cnf(c_1666,plain,
    ( sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1585])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_512,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_513,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r2_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_23])).

cnf(c_516,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_493,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r1_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_23])).

cnf(c_496,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | k9_eqrel_1(sK0,sK1,sK2) != X2
    | k3_filter_1(sK0,sK1,sK3) != X0
    | k8_eqrel_1(sK0,sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_471,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_13,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_438,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_14,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_423,plain,
    ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_424,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_15,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_409,plain,
    ( v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_410,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_28])).

cnf(c_413,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_90,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1834,c_1835,c_1836,c_1807,c_1724,c_1721,c_1718,c_1666,c_516,c_496,c_471,c_438,c_424,c_413,c_90,c_23,c_24,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:11:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/1.00  
% 1.71/1.00  ------  iProver source info
% 1.71/1.00  
% 1.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/1.00  git: non_committed_changes: false
% 1.71/1.00  git: last_make_outside_of_git: false
% 1.71/1.00  
% 1.71/1.00  ------ 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options
% 1.71/1.00  
% 1.71/1.00  --out_options                           all
% 1.71/1.00  --tptp_safe_out                         true
% 1.71/1.00  --problem_path                          ""
% 1.71/1.00  --include_path                          ""
% 1.71/1.00  --clausifier                            res/vclausify_rel
% 1.71/1.00  --clausifier_options                    --mode clausify
% 1.71/1.00  --stdin                                 false
% 1.71/1.00  --stats_out                             all
% 1.71/1.00  
% 1.71/1.00  ------ General Options
% 1.71/1.00  
% 1.71/1.00  --fof                                   false
% 1.71/1.00  --time_out_real                         305.
% 1.71/1.00  --time_out_virtual                      -1.
% 1.71/1.00  --symbol_type_check                     false
% 1.71/1.00  --clausify_out                          false
% 1.71/1.00  --sig_cnt_out                           false
% 1.71/1.00  --trig_cnt_out                          false
% 1.71/1.00  --trig_cnt_out_tolerance                1.
% 1.71/1.00  --trig_cnt_out_sk_spl                   false
% 1.71/1.00  --abstr_cl_out                          false
% 1.71/1.00  
% 1.71/1.00  ------ Global Options
% 1.71/1.00  
% 1.71/1.00  --schedule                              default
% 1.71/1.00  --add_important_lit                     false
% 1.71/1.00  --prop_solver_per_cl                    1000
% 1.71/1.00  --min_unsat_core                        false
% 1.71/1.00  --soft_assumptions                      false
% 1.71/1.00  --soft_lemma_size                       3
% 1.71/1.00  --prop_impl_unit_size                   0
% 1.71/1.00  --prop_impl_unit                        []
% 1.71/1.00  --share_sel_clauses                     true
% 1.71/1.00  --reset_solvers                         false
% 1.71/1.00  --bc_imp_inh                            [conj_cone]
% 1.71/1.00  --conj_cone_tolerance                   3.
% 1.71/1.00  --extra_neg_conj                        none
% 1.71/1.00  --large_theory_mode                     true
% 1.71/1.00  --prolific_symb_bound                   200
% 1.71/1.00  --lt_threshold                          2000
% 1.71/1.00  --clause_weak_htbl                      true
% 1.71/1.00  --gc_record_bc_elim                     false
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing Options
% 1.71/1.00  
% 1.71/1.00  --preprocessing_flag                    true
% 1.71/1.00  --time_out_prep_mult                    0.1
% 1.71/1.00  --splitting_mode                        input
% 1.71/1.00  --splitting_grd                         true
% 1.71/1.00  --splitting_cvd                         false
% 1.71/1.00  --splitting_cvd_svl                     false
% 1.71/1.00  --splitting_nvd                         32
% 1.71/1.00  --sub_typing                            true
% 1.71/1.00  --prep_gs_sim                           true
% 1.71/1.00  --prep_unflatten                        true
% 1.71/1.00  --prep_res_sim                          true
% 1.71/1.00  --prep_upred                            true
% 1.71/1.00  --prep_sem_filter                       exhaustive
% 1.71/1.00  --prep_sem_filter_out                   false
% 1.71/1.00  --pred_elim                             true
% 1.71/1.00  --res_sim_input                         true
% 1.71/1.00  --eq_ax_congr_red                       true
% 1.71/1.00  --pure_diseq_elim                       true
% 1.71/1.00  --brand_transform                       false
% 1.71/1.00  --non_eq_to_eq                          false
% 1.71/1.00  --prep_def_merge                        true
% 1.71/1.00  --prep_def_merge_prop_impl              false
% 1.71/1.00  --prep_def_merge_mbd                    true
% 1.71/1.00  --prep_def_merge_tr_red                 false
% 1.71/1.00  --prep_def_merge_tr_cl                  false
% 1.71/1.00  --smt_preprocessing                     true
% 1.71/1.00  --smt_ac_axioms                         fast
% 1.71/1.00  --preprocessed_out                      false
% 1.71/1.00  --preprocessed_stats                    false
% 1.71/1.00  
% 1.71/1.00  ------ Abstraction refinement Options
% 1.71/1.00  
% 1.71/1.00  --abstr_ref                             []
% 1.71/1.00  --abstr_ref_prep                        false
% 1.71/1.00  --abstr_ref_until_sat                   false
% 1.71/1.00  --abstr_ref_sig_restrict                funpre
% 1.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.00  --abstr_ref_under                       []
% 1.71/1.00  
% 1.71/1.00  ------ SAT Options
% 1.71/1.00  
% 1.71/1.00  --sat_mode                              false
% 1.71/1.00  --sat_fm_restart_options                ""
% 1.71/1.00  --sat_gr_def                            false
% 1.71/1.00  --sat_epr_types                         true
% 1.71/1.00  --sat_non_cyclic_types                  false
% 1.71/1.00  --sat_finite_models                     false
% 1.71/1.00  --sat_fm_lemmas                         false
% 1.71/1.00  --sat_fm_prep                           false
% 1.71/1.00  --sat_fm_uc_incr                        true
% 1.71/1.00  --sat_out_model                         small
% 1.71/1.00  --sat_out_clauses                       false
% 1.71/1.00  
% 1.71/1.00  ------ QBF Options
% 1.71/1.00  
% 1.71/1.00  --qbf_mode                              false
% 1.71/1.00  --qbf_elim_univ                         false
% 1.71/1.00  --qbf_dom_inst                          none
% 1.71/1.00  --qbf_dom_pre_inst                      false
% 1.71/1.00  --qbf_sk_in                             false
% 1.71/1.00  --qbf_pred_elim                         true
% 1.71/1.00  --qbf_split                             512
% 1.71/1.00  
% 1.71/1.00  ------ BMC1 Options
% 1.71/1.00  
% 1.71/1.00  --bmc1_incremental                      false
% 1.71/1.00  --bmc1_axioms                           reachable_all
% 1.71/1.00  --bmc1_min_bound                        0
% 1.71/1.00  --bmc1_max_bound                        -1
% 1.71/1.00  --bmc1_max_bound_default                -1
% 1.71/1.00  --bmc1_symbol_reachability              true
% 1.71/1.00  --bmc1_property_lemmas                  false
% 1.71/1.00  --bmc1_k_induction                      false
% 1.71/1.00  --bmc1_non_equiv_states                 false
% 1.71/1.00  --bmc1_deadlock                         false
% 1.71/1.00  --bmc1_ucm                              false
% 1.71/1.00  --bmc1_add_unsat_core                   none
% 1.71/1.00  --bmc1_unsat_core_children              false
% 1.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.00  --bmc1_out_stat                         full
% 1.71/1.00  --bmc1_ground_init                      false
% 1.71/1.00  --bmc1_pre_inst_next_state              false
% 1.71/1.00  --bmc1_pre_inst_state                   false
% 1.71/1.00  --bmc1_pre_inst_reach_state             false
% 1.71/1.00  --bmc1_out_unsat_core                   false
% 1.71/1.00  --bmc1_aig_witness_out                  false
% 1.71/1.00  --bmc1_verbose                          false
% 1.71/1.00  --bmc1_dump_clauses_tptp                false
% 1.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.00  --bmc1_dump_file                        -
% 1.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.00  --bmc1_ucm_extend_mode                  1
% 1.71/1.00  --bmc1_ucm_init_mode                    2
% 1.71/1.00  --bmc1_ucm_cone_mode                    none
% 1.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.00  --bmc1_ucm_relax_model                  4
% 1.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.00  --bmc1_ucm_layered_model                none
% 1.71/1.00  --bmc1_ucm_max_lemma_size               10
% 1.71/1.00  
% 1.71/1.00  ------ AIG Options
% 1.71/1.00  
% 1.71/1.00  --aig_mode                              false
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation Options
% 1.71/1.00  
% 1.71/1.00  --instantiation_flag                    true
% 1.71/1.00  --inst_sos_flag                         false
% 1.71/1.00  --inst_sos_phase                        true
% 1.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel_side                     num_symb
% 1.71/1.00  --inst_solver_per_active                1400
% 1.71/1.00  --inst_solver_calls_frac                1.
% 1.71/1.00  --inst_passive_queue_type               priority_queues
% 1.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.00  --inst_passive_queues_freq              [25;2]
% 1.71/1.00  --inst_dismatching                      true
% 1.71/1.00  --inst_eager_unprocessed_to_passive     true
% 1.71/1.00  --inst_prop_sim_given                   true
% 1.71/1.00  --inst_prop_sim_new                     false
% 1.71/1.00  --inst_subs_new                         false
% 1.71/1.00  --inst_eq_res_simp                      false
% 1.71/1.00  --inst_subs_given                       false
% 1.71/1.00  --inst_orphan_elimination               true
% 1.71/1.00  --inst_learning_loop_flag               true
% 1.71/1.00  --inst_learning_start                   3000
% 1.71/1.00  --inst_learning_factor                  2
% 1.71/1.00  --inst_start_prop_sim_after_learn       3
% 1.71/1.00  --inst_sel_renew                        solver
% 1.71/1.00  --inst_lit_activity_flag                true
% 1.71/1.00  --inst_restr_to_given                   false
% 1.71/1.00  --inst_activity_threshold               500
% 1.71/1.00  --inst_out_proof                        true
% 1.71/1.00  
% 1.71/1.00  ------ Resolution Options
% 1.71/1.00  
% 1.71/1.00  --resolution_flag                       true
% 1.71/1.00  --res_lit_sel                           adaptive
% 1.71/1.00  --res_lit_sel_side                      none
% 1.71/1.00  --res_ordering                          kbo
% 1.71/1.00  --res_to_prop_solver                    active
% 1.71/1.00  --res_prop_simpl_new                    false
% 1.71/1.00  --res_prop_simpl_given                  true
% 1.71/1.00  --res_passive_queue_type                priority_queues
% 1.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.00  --res_passive_queues_freq               [15;5]
% 1.71/1.00  --res_forward_subs                      full
% 1.71/1.00  --res_backward_subs                     full
% 1.71/1.00  --res_forward_subs_resolution           true
% 1.71/1.00  --res_backward_subs_resolution          true
% 1.71/1.00  --res_orphan_elimination                true
% 1.71/1.00  --res_time_limit                        2.
% 1.71/1.00  --res_out_proof                         true
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Options
% 1.71/1.00  
% 1.71/1.00  --superposition_flag                    true
% 1.71/1.00  --sup_passive_queue_type                priority_queues
% 1.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.00  --demod_completeness_check              fast
% 1.71/1.00  --demod_use_ground                      true
% 1.71/1.00  --sup_to_prop_solver                    passive
% 1.71/1.00  --sup_prop_simpl_new                    true
% 1.71/1.00  --sup_prop_simpl_given                  true
% 1.71/1.00  --sup_fun_splitting                     false
% 1.71/1.00  --sup_smt_interval                      50000
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Simplification Setup
% 1.71/1.00  
% 1.71/1.00  --sup_indices_passive                   []
% 1.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_full_bw                           [BwDemod]
% 1.71/1.00  --sup_immed_triv                        [TrivRules]
% 1.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_immed_bw_main                     []
% 1.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  
% 1.71/1.00  ------ Combination Options
% 1.71/1.00  
% 1.71/1.00  --comb_res_mult                         3
% 1.71/1.00  --comb_sup_mult                         2
% 1.71/1.00  --comb_inst_mult                        10
% 1.71/1.00  
% 1.71/1.00  ------ Debug Options
% 1.71/1.00  
% 1.71/1.00  --dbg_backtrace                         false
% 1.71/1.00  --dbg_dump_prop_clauses                 false
% 1.71/1.00  --dbg_dump_prop_clauses_file            -
% 1.71/1.00  --dbg_out_stat                          false
% 1.71/1.00  ------ Parsing...
% 1.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/1.00  ------ Proving...
% 1.71/1.00  ------ Problem Properties 
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  clauses                                 23
% 1.71/1.00  conjectures                             3
% 1.71/1.00  EPR                                     3
% 1.71/1.00  Horn                                    22
% 1.71/1.00  unary                                   7
% 1.71/1.00  binary                                  3
% 1.71/1.00  lits                                    60
% 1.71/1.00  lits eq                                 4
% 1.71/1.00  fd_pure                                 0
% 1.71/1.00  fd_pseudo                               0
% 1.71/1.00  fd_cond                                 0
% 1.71/1.00  fd_pseudo_cond                          0
% 1.71/1.00  AC symbols                              0
% 1.71/1.00  
% 1.71/1.00  ------ Schedule dynamic 5 is on 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  ------ 
% 1.71/1.00  Current options:
% 1.71/1.00  ------ 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options
% 1.71/1.00  
% 1.71/1.00  --out_options                           all
% 1.71/1.00  --tptp_safe_out                         true
% 1.71/1.00  --problem_path                          ""
% 1.71/1.00  --include_path                          ""
% 1.71/1.00  --clausifier                            res/vclausify_rel
% 1.71/1.00  --clausifier_options                    --mode clausify
% 1.71/1.00  --stdin                                 false
% 1.71/1.00  --stats_out                             all
% 1.71/1.00  
% 1.71/1.00  ------ General Options
% 1.71/1.00  
% 1.71/1.00  --fof                                   false
% 1.71/1.00  --time_out_real                         305.
% 1.71/1.00  --time_out_virtual                      -1.
% 1.71/1.00  --symbol_type_check                     false
% 1.71/1.00  --clausify_out                          false
% 1.71/1.00  --sig_cnt_out                           false
% 1.71/1.00  --trig_cnt_out                          false
% 1.71/1.00  --trig_cnt_out_tolerance                1.
% 1.71/1.00  --trig_cnt_out_sk_spl                   false
% 1.71/1.00  --abstr_cl_out                          false
% 1.71/1.00  
% 1.71/1.00  ------ Global Options
% 1.71/1.00  
% 1.71/1.00  --schedule                              default
% 1.71/1.00  --add_important_lit                     false
% 1.71/1.00  --prop_solver_per_cl                    1000
% 1.71/1.00  --min_unsat_core                        false
% 1.71/1.00  --soft_assumptions                      false
% 1.71/1.00  --soft_lemma_size                       3
% 1.71/1.00  --prop_impl_unit_size                   0
% 1.71/1.00  --prop_impl_unit                        []
% 1.71/1.00  --share_sel_clauses                     true
% 1.71/1.00  --reset_solvers                         false
% 1.71/1.00  --bc_imp_inh                            [conj_cone]
% 1.71/1.00  --conj_cone_tolerance                   3.
% 1.71/1.00  --extra_neg_conj                        none
% 1.71/1.00  --large_theory_mode                     true
% 1.71/1.00  --prolific_symb_bound                   200
% 1.71/1.00  --lt_threshold                          2000
% 1.71/1.00  --clause_weak_htbl                      true
% 1.71/1.00  --gc_record_bc_elim                     false
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing Options
% 1.71/1.00  
% 1.71/1.00  --preprocessing_flag                    true
% 1.71/1.00  --time_out_prep_mult                    0.1
% 1.71/1.00  --splitting_mode                        input
% 1.71/1.00  --splitting_grd                         true
% 1.71/1.00  --splitting_cvd                         false
% 1.71/1.00  --splitting_cvd_svl                     false
% 1.71/1.00  --splitting_nvd                         32
% 1.71/1.00  --sub_typing                            true
% 1.71/1.00  --prep_gs_sim                           true
% 1.71/1.00  --prep_unflatten                        true
% 1.71/1.00  --prep_res_sim                          true
% 1.71/1.00  --prep_upred                            true
% 1.71/1.00  --prep_sem_filter                       exhaustive
% 1.71/1.00  --prep_sem_filter_out                   false
% 1.71/1.00  --pred_elim                             true
% 1.71/1.00  --res_sim_input                         true
% 1.71/1.00  --eq_ax_congr_red                       true
% 1.71/1.00  --pure_diseq_elim                       true
% 1.71/1.00  --brand_transform                       false
% 1.71/1.00  --non_eq_to_eq                          false
% 1.71/1.00  --prep_def_merge                        true
% 1.71/1.00  --prep_def_merge_prop_impl              false
% 1.71/1.00  --prep_def_merge_mbd                    true
% 1.71/1.00  --prep_def_merge_tr_red                 false
% 1.71/1.00  --prep_def_merge_tr_cl                  false
% 1.71/1.00  --smt_preprocessing                     true
% 1.71/1.00  --smt_ac_axioms                         fast
% 1.71/1.00  --preprocessed_out                      false
% 1.71/1.00  --preprocessed_stats                    false
% 1.71/1.00  
% 1.71/1.00  ------ Abstraction refinement Options
% 1.71/1.00  
% 1.71/1.00  --abstr_ref                             []
% 1.71/1.00  --abstr_ref_prep                        false
% 1.71/1.00  --abstr_ref_until_sat                   false
% 1.71/1.00  --abstr_ref_sig_restrict                funpre
% 1.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.00  --abstr_ref_under                       []
% 1.71/1.00  
% 1.71/1.00  ------ SAT Options
% 1.71/1.00  
% 1.71/1.00  --sat_mode                              false
% 1.71/1.00  --sat_fm_restart_options                ""
% 1.71/1.00  --sat_gr_def                            false
% 1.71/1.00  --sat_epr_types                         true
% 1.71/1.00  --sat_non_cyclic_types                  false
% 1.71/1.00  --sat_finite_models                     false
% 1.71/1.00  --sat_fm_lemmas                         false
% 1.71/1.00  --sat_fm_prep                           false
% 1.71/1.00  --sat_fm_uc_incr                        true
% 1.71/1.00  --sat_out_model                         small
% 1.71/1.00  --sat_out_clauses                       false
% 1.71/1.00  
% 1.71/1.00  ------ QBF Options
% 1.71/1.00  
% 1.71/1.00  --qbf_mode                              false
% 1.71/1.00  --qbf_elim_univ                         false
% 1.71/1.00  --qbf_dom_inst                          none
% 1.71/1.00  --qbf_dom_pre_inst                      false
% 1.71/1.00  --qbf_sk_in                             false
% 1.71/1.00  --qbf_pred_elim                         true
% 1.71/1.00  --qbf_split                             512
% 1.71/1.00  
% 1.71/1.00  ------ BMC1 Options
% 1.71/1.00  
% 1.71/1.00  --bmc1_incremental                      false
% 1.71/1.00  --bmc1_axioms                           reachable_all
% 1.71/1.00  --bmc1_min_bound                        0
% 1.71/1.00  --bmc1_max_bound                        -1
% 1.71/1.00  --bmc1_max_bound_default                -1
% 1.71/1.00  --bmc1_symbol_reachability              true
% 1.71/1.00  --bmc1_property_lemmas                  false
% 1.71/1.00  --bmc1_k_induction                      false
% 1.71/1.00  --bmc1_non_equiv_states                 false
% 1.71/1.00  --bmc1_deadlock                         false
% 1.71/1.00  --bmc1_ucm                              false
% 1.71/1.00  --bmc1_add_unsat_core                   none
% 1.71/1.00  --bmc1_unsat_core_children              false
% 1.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.00  --bmc1_out_stat                         full
% 1.71/1.00  --bmc1_ground_init                      false
% 1.71/1.00  --bmc1_pre_inst_next_state              false
% 1.71/1.00  --bmc1_pre_inst_state                   false
% 1.71/1.00  --bmc1_pre_inst_reach_state             false
% 1.71/1.00  --bmc1_out_unsat_core                   false
% 1.71/1.00  --bmc1_aig_witness_out                  false
% 1.71/1.00  --bmc1_verbose                          false
% 1.71/1.00  --bmc1_dump_clauses_tptp                false
% 1.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.00  --bmc1_dump_file                        -
% 1.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.00  --bmc1_ucm_extend_mode                  1
% 1.71/1.00  --bmc1_ucm_init_mode                    2
% 1.71/1.00  --bmc1_ucm_cone_mode                    none
% 1.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.00  --bmc1_ucm_relax_model                  4
% 1.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.00  --bmc1_ucm_layered_model                none
% 1.71/1.00  --bmc1_ucm_max_lemma_size               10
% 1.71/1.00  
% 1.71/1.00  ------ AIG Options
% 1.71/1.00  
% 1.71/1.00  --aig_mode                              false
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation Options
% 1.71/1.00  
% 1.71/1.00  --instantiation_flag                    true
% 1.71/1.00  --inst_sos_flag                         false
% 1.71/1.00  --inst_sos_phase                        true
% 1.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel_side                     none
% 1.71/1.00  --inst_solver_per_active                1400
% 1.71/1.00  --inst_solver_calls_frac                1.
% 1.71/1.00  --inst_passive_queue_type               priority_queues
% 1.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.00  --inst_passive_queues_freq              [25;2]
% 1.71/1.00  --inst_dismatching                      true
% 1.71/1.00  --inst_eager_unprocessed_to_passive     true
% 1.71/1.00  --inst_prop_sim_given                   true
% 1.71/1.00  --inst_prop_sim_new                     false
% 1.71/1.00  --inst_subs_new                         false
% 1.71/1.00  --inst_eq_res_simp                      false
% 1.71/1.00  --inst_subs_given                       false
% 1.71/1.00  --inst_orphan_elimination               true
% 1.71/1.00  --inst_learning_loop_flag               true
% 1.71/1.00  --inst_learning_start                   3000
% 1.71/1.00  --inst_learning_factor                  2
% 1.71/1.00  --inst_start_prop_sim_after_learn       3
% 1.71/1.00  --inst_sel_renew                        solver
% 1.71/1.00  --inst_lit_activity_flag                true
% 1.71/1.00  --inst_restr_to_given                   false
% 1.71/1.00  --inst_activity_threshold               500
% 1.71/1.00  --inst_out_proof                        true
% 1.71/1.00  
% 1.71/1.00  ------ Resolution Options
% 1.71/1.00  
% 1.71/1.00  --resolution_flag                       false
% 1.71/1.00  --res_lit_sel                           adaptive
% 1.71/1.00  --res_lit_sel_side                      none
% 1.71/1.00  --res_ordering                          kbo
% 1.71/1.00  --res_to_prop_solver                    active
% 1.71/1.00  --res_prop_simpl_new                    false
% 1.71/1.00  --res_prop_simpl_given                  true
% 1.71/1.00  --res_passive_queue_type                priority_queues
% 1.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.00  --res_passive_queues_freq               [15;5]
% 1.71/1.00  --res_forward_subs                      full
% 1.71/1.00  --res_backward_subs                     full
% 1.71/1.00  --res_forward_subs_resolution           true
% 1.71/1.00  --res_backward_subs_resolution          true
% 1.71/1.00  --res_orphan_elimination                true
% 1.71/1.00  --res_time_limit                        2.
% 1.71/1.00  --res_out_proof                         true
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Options
% 1.71/1.00  
% 1.71/1.00  --superposition_flag                    true
% 1.71/1.00  --sup_passive_queue_type                priority_queues
% 1.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.00  --demod_completeness_check              fast
% 1.71/1.00  --demod_use_ground                      true
% 1.71/1.00  --sup_to_prop_solver                    passive
% 1.71/1.00  --sup_prop_simpl_new                    true
% 1.71/1.00  --sup_prop_simpl_given                  true
% 1.71/1.00  --sup_fun_splitting                     false
% 1.71/1.00  --sup_smt_interval                      50000
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Simplification Setup
% 1.71/1.00  
% 1.71/1.00  --sup_indices_passive                   []
% 1.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_full_bw                           [BwDemod]
% 1.71/1.00  --sup_immed_triv                        [TrivRules]
% 1.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_immed_bw_main                     []
% 1.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  
% 1.71/1.00  ------ Combination Options
% 1.71/1.00  
% 1.71/1.00  --comb_res_mult                         3
% 1.71/1.00  --comb_sup_mult                         2
% 1.71/1.00  --comb_inst_mult                        10
% 1.71/1.00  
% 1.71/1.00  ------ Debug Options
% 1.71/1.00  
% 1.71/1.00  --dbg_backtrace                         false
% 1.71/1.00  --dbg_dump_prop_clauses                 false
% 1.71/1.00  --dbg_dump_prop_clauses_file            -
% 1.71/1.00  --dbg_out_stat                          false
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  ------ Proving...
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  % SZS status Theorem for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  fof(f14,conjecture,(
% 1.71/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f15,negated_conjecture,(
% 1.71/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.71/1.00    inference(negated_conjecture,[],[f14])).
% 1.71/1.00  
% 1.71/1.00  fof(f38,plain,(
% 1.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f15])).
% 1.71/1.00  
% 1.71/1.00  fof(f39,plain,(
% 1.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f38])).
% 1.71/1.00  
% 1.71/1.00  fof(f46,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) => (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3)) & r3_binop_1(X0,X2,sK3) & m2_filter_1(sK3,X0,X1))) )),
% 1.71/1.00    introduced(choice_axiom,[])).
% 1.71/1.00  
% 1.71/1.00  fof(f45,plain,(
% 1.71/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,sK2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(sK2,X0))) )),
% 1.71/1.00    introduced(choice_axiom,[])).
% 1.71/1.00  
% 1.71/1.00  fof(f44,plain,(
% 1.71/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,sK1)) & m1_subset_1(X2,X0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,X0))) )),
% 1.71/1.00    introduced(choice_axiom,[])).
% 1.71/1.00  
% 1.71/1.00  fof(f43,plain,(
% 1.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.71/1.00    introduced(choice_axiom,[])).
% 1.71/1.00  
% 1.71/1.00  fof(f47,plain,(
% 1.71/1.00    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f46,f45,f44,f43])).
% 1.71/1.00  
% 1.71/1.00  fof(f69,plain,(
% 1.71/1.00    v1_partfun1(sK1,sK0)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f6,axiom,(
% 1.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f22,plain,(
% 1.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f6])).
% 1.71/1.00  
% 1.71/1.00  fof(f23,plain,(
% 1.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f22])).
% 1.71/1.00  
% 1.71/1.00  fof(f56,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k3_filter_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f23])).
% 1.71/1.00  
% 1.71/1.00  fof(f71,plain,(
% 1.71/1.00    v8_relat_2(sK1)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f70,plain,(
% 1.71/1.00    v3_relat_2(sK1)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f68,plain,(
% 1.71/1.00    ~v1_xboole_0(sK0)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f72,plain,(
% 1.71/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f57,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f23])).
% 1.71/1.00  
% 1.71/1.00  fof(f58,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f23])).
% 1.71/1.00  
% 1.71/1.00  fof(f2,axiom,(
% 1.71/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f17,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f2])).
% 1.71/1.00  
% 1.71/1.00  fof(f49,plain,(
% 1.71/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f17])).
% 1.71/1.00  
% 1.71/1.00  fof(f12,axiom,(
% 1.71/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f34,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f12])).
% 1.71/1.00  
% 1.71/1.00  fof(f35,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f34])).
% 1.71/1.00  
% 1.71/1.00  fof(f66,plain,(
% 1.71/1.00    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f35])).
% 1.71/1.00  
% 1.71/1.00  fof(f74,plain,(
% 1.71/1.00    m2_filter_1(sK3,sK0,sK1)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f13,axiom,(
% 1.71/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f36,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f13])).
% 1.71/1.00  
% 1.71/1.00  fof(f37,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f36])).
% 1.71/1.00  
% 1.71/1.00  fof(f67,plain,(
% 1.71/1.00    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f37])).
% 1.71/1.00  
% 1.71/1.00  fof(f4,axiom,(
% 1.71/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f18,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f4])).
% 1.71/1.00  
% 1.71/1.00  fof(f19,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f18])).
% 1.71/1.00  
% 1.71/1.00  fof(f40,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.71/1.00    inference(nnf_transformation,[],[f19])).
% 1.71/1.00  
% 1.71/1.00  fof(f51,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f40])).
% 1.71/1.00  
% 1.71/1.00  fof(f8,axiom,(
% 1.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f26,plain,(
% 1.71/1.00    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f8])).
% 1.71/1.00  
% 1.71/1.00  fof(f27,plain,(
% 1.71/1.00    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f26])).
% 1.71/1.00  
% 1.71/1.00  fof(f60,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f27])).
% 1.71/1.00  
% 1.71/1.00  fof(f1,axiom,(
% 1.71/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f16,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f1])).
% 1.71/1.00  
% 1.71/1.00  fof(f48,plain,(
% 1.71/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f16])).
% 1.71/1.00  
% 1.71/1.00  fof(f10,axiom,(
% 1.71/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f30,plain,(
% 1.71/1.00    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f10])).
% 1.71/1.00  
% 1.71/1.00  fof(f31,plain,(
% 1.71/1.00    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f30])).
% 1.71/1.00  
% 1.71/1.00  fof(f64,plain,(
% 1.71/1.00    ( ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f31])).
% 1.71/1.00  
% 1.71/1.00  fof(f11,axiom,(
% 1.71/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f32,plain,(
% 1.71/1.00    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.71/1.00    inference(ennf_transformation,[],[f11])).
% 1.71/1.00  
% 1.71/1.00  fof(f33,plain,(
% 1.71/1.00    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.71/1.00    inference(flattening,[],[f32])).
% 1.71/1.00  
% 1.71/1.00  fof(f65,plain,(
% 1.71/1.00    ( ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f33])).
% 1.71/1.00  
% 1.71/1.00  fof(f7,axiom,(
% 1.71/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f24,plain,(
% 1.71/1.00    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.71/1.00    inference(ennf_transformation,[],[f7])).
% 1.71/1.00  
% 1.71/1.00  fof(f25,plain,(
% 1.71/1.00    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.71/1.00    inference(flattening,[],[f24])).
% 1.71/1.00  
% 1.71/1.00  fof(f59,plain,(
% 1.71/1.00    ( ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f25])).
% 1.71/1.00  
% 1.71/1.00  fof(f5,axiom,(
% 1.71/1.00    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f20,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f5])).
% 1.71/1.00  
% 1.71/1.00  fof(f21,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.71/1.00    inference(flattening,[],[f20])).
% 1.71/1.00  
% 1.71/1.00  fof(f41,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.71/1.00    inference(nnf_transformation,[],[f21])).
% 1.71/1.00  
% 1.71/1.00  fof(f42,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.71/1.00    inference(flattening,[],[f41])).
% 1.71/1.00  
% 1.71/1.00  fof(f54,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f42])).
% 1.71/1.00  
% 1.71/1.00  fof(f75,plain,(
% 1.71/1.00    r3_binop_1(sK0,sK2,sK3)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f73,plain,(
% 1.71/1.00    m1_subset_1(sK2,sK0)),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f53,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f42])).
% 1.71/1.00  
% 1.71/1.00  fof(f55,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f42])).
% 1.71/1.00  
% 1.71/1.00  fof(f76,plain,(
% 1.71/1.00    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.71/1.00    inference(cnf_transformation,[],[f47])).
% 1.71/1.00  
% 1.71/1.00  fof(f9,axiom,(
% 1.71/1.00    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f28,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f9])).
% 1.71/1.00  
% 1.71/1.00  fof(f29,plain,(
% 1.71/1.00    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 1.71/1.00    inference(flattening,[],[f28])).
% 1.71/1.00  
% 1.71/1.00  fof(f63,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f29])).
% 1.71/1.00  
% 1.71/1.00  fof(f62,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f29])).
% 1.71/1.00  
% 1.71/1.00  fof(f61,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f29])).
% 1.71/1.00  
% 1.71/1.00  fof(f3,axiom,(
% 1.71/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f50,plain,(
% 1.71/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/1.00    inference(cnf_transformation,[],[f3])).
% 1.71/1.00  
% 1.71/1.00  cnf(c_27,negated_conjecture,
% 1.71/1.00      ( v1_partfun1(sK1,sK0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_10,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v8_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_25,negated_conjecture,
% 1.71/1.00      ( v8_relat_2(sK1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_661,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,X2,X0))
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != X2 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_662,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_661]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_26,negated_conjecture,
% 1.71/1.00      ( v3_relat_2(sK1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_666,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_662,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_667,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_666]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_907,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(X1,sK1,X0))
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_667]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_908,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_907]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_28,negated_conjecture,
% 1.71/1.00      ( ~ v1_xboole_0(sK0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_24,negated_conjecture,
% 1.71/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.71/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_912,plain,
% 1.71/1.00      ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_908,c_28,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_913,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_funct_1(k3_filter_1(sK0,sK1,X0)) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_912]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1834,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_913]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_9,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v8_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_694,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != X2 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_695,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_694]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_699,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_695,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_700,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_699]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_883,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_700]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_884,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_883]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_888,plain,
% 1.71/1.00      ( ~ v1_funct_1(X0)
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_884,c_28,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_889,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(X0) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_888]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1835,plain,
% 1.71/1.00      ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_889]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_8,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v8_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_727,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != X2 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_728,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_727]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_732,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_728,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_733,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_partfun1(sK1,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_732]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_859,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_733]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_860,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_859]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_864,plain,
% 1.71/1.00      ( ~ v1_funct_1(X0)
% 1.71/1.00      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_860,c_28,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_865,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.71/1.00      | ~ v1_funct_1(X0) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_864]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1836,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_865]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.71/1.00      | ~ v1_relat_1(X1)
% 1.71/1.00      | v1_relat_1(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1730,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.71/1.00      | v1_relat_1(X0)
% 1.71/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1807,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 1.71/1.00      | v1_relat_1(sK1) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_1730]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_18,plain,
% 1.71/1.00      ( ~ m2_filter_1(X0,X1,X2)
% 1.71/1.00      | ~ r1_binop_1(X1,X3,X0)
% 1.71/1.00      | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X3,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v8_relat_2(X2)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_22,negated_conjecture,
% 1.71/1.00      ( m2_filter_1(sK3,sK0,sK1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_388,plain,
% 1.71/1.00      ( ~ r1_binop_1(X0,X1,X2)
% 1.71/1.00      | r1_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.71/1.00      | ~ v1_partfun1(X3,X0)
% 1.71/1.00      | ~ m1_subset_1(X1,X0)
% 1.71/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(X3)
% 1.71/1.00      | ~ v8_relat_2(X3)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | sK3 != X2
% 1.71/1.00      | sK1 != X3
% 1.71/1.00      | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_389,plain,
% 1.71/1.00      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r1_binop_1(sK0,X0,sK3)
% 1.71/1.00      | ~ v1_partfun1(sK1,sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v8_relat_2(sK1)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_393,plain,
% 1.71/1.00      ( ~ r1_binop_1(sK0,X0,sK3)
% 1.71/1.00      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ m1_subset_1(X0,sK0) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_389,c_28,c_27,c_26,c_25,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_394,plain,
% 1.71/1.00      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r1_binop_1(sK0,X0,sK3)
% 1.71/1.00      | ~ m1_subset_1(X0,sK0) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_393]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1724,plain,
% 1.71/1.00      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r1_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK2,sK0) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_394]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_19,plain,
% 1.71/1.00      ( ~ m2_filter_1(X0,X1,X2)
% 1.71/1.00      | ~ r2_binop_1(X1,X3,X0)
% 1.71/1.00      | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
% 1.71/1.00      | ~ v1_partfun1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X3,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X2)
% 1.71/1.00      | ~ v8_relat_2(X2)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_367,plain,
% 1.71/1.00      ( ~ r2_binop_1(X0,X1,X2)
% 1.71/1.00      | r2_binop_1(k8_eqrel_1(X0,X3),k9_eqrel_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
% 1.71/1.00      | ~ v1_partfun1(X3,X0)
% 1.71/1.00      | ~ m1_subset_1(X1,X0)
% 1.71/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(X3)
% 1.71/1.00      | ~ v8_relat_2(X3)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | sK3 != X2
% 1.71/1.00      | sK1 != X3
% 1.71/1.00      | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_368,plain,
% 1.71/1.00      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r2_binop_1(sK0,X0,sK3)
% 1.71/1.00      | ~ v1_partfun1(sK1,sK0)
% 1.71/1.00      | ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v8_relat_2(sK1)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_367]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_372,plain,
% 1.71/1.00      ( ~ r2_binop_1(sK0,X0,sK3)
% 1.71/1.00      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ m1_subset_1(X0,sK0) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_368,c_28,c_27,c_26,c_25,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_373,plain,
% 1.71/1.00      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r2_binop_1(sK0,X0,sK3)
% 1.71/1.00      | ~ m1_subset_1(X0,sK0) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_372]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1721,plain,
% 1.71/1.00      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r2_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK2,sK0) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_373]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_4,plain,
% 1.71/1.00      ( ~ m2_subset_1(X0,X1,X2)
% 1.71/1.00      | m1_subset_1(X0,X2)
% 1.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(X2) ),
% 1.71/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_12,plain,
% 1.71/1.00      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
% 1.71/1.00      | ~ v1_partfun1(X1,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(X1)
% 1.71/1.00      | ~ v8_relat_2(X1)
% 1.71/1.00      | v1_xboole_0(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_319,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | m1_subset_1(X3,X4)
% 1.71/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X5)
% 1.71/1.00      | v1_xboole_0(X4)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | k9_eqrel_1(X1,X0,X2) != X3
% 1.71/1.00      | k8_eqrel_1(X1,X0) != X4
% 1.71/1.00      | k1_zfmisc_1(X1) != X5 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_320,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.71/1.00      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_0,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.71/1.00      | ~ v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_344,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X1,X0)) ),
% 1.71/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_320,c_0]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_562,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X1,X0))
% 1.71/1.00      | sK1 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_344,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_563,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(X1,X0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_567,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.71/1.00      | ~ m1_subset_1(X1,X0)
% 1.71/1.00      | ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_563,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_568,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(X1,X0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X0,sK1,X1),k8_eqrel_1(X0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_567]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_835,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,X1)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(X1,sK1,X0),k8_eqrel_1(X1,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(X1,sK1),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(X1,sK1))
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_568]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_836,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_835]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_840,plain,
% 1.71/1.00      ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_836,c_28,c_24]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_841,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_840]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1095,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,sK0)
% 1.71/1.00      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ sP0_iProver_split ),
% 1.71/1.00      inference(splitting,
% 1.71/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.71/1.00                [c_841]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1718,plain,
% 1.71/1.00      ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(sK2,sK0)
% 1.71/1.00      | ~ sP0_iProver_split ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1096,plain,
% 1.71/1.00      ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | sP0_iProver_split ),
% 1.71/1.00      inference(splitting,
% 1.71/1.00                [splitting(split),new_symbols(definition,[])],
% 1.71/1.00                [c_841]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1524,plain,
% 1.71/1.00      ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 1.71/1.00      | v1_xboole_0(k8_eqrel_1(sK0,sK1)) = iProver_top
% 1.71/1.00      | sP0_iProver_split = iProver_top ),
% 1.71/1.00      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_16,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X1,X0)) ),
% 1.71/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_616,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X1,X0))
% 1.71/1.00      | sK1 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_617,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_616]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_621,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_617,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_622,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1)) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_621]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_816,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | v1_xboole_0(X0)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(X0,sK1))
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_622]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_817,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_816]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_619,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,sK0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_617]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_819,plain,
% 1.71/1.00      ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_817,c_28,c_27,c_26,c_24,c_619]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1526,plain,
% 1.71/1.00      ( v1_xboole_0(k7_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.71/1.00      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_17,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0)
% 1.71/1.00      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_595,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
% 1.71/1.00      | sK1 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_596,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_595]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_600,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_596,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_601,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_600]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_827,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | k7_eqrel_1(X0,sK1) = k8_eqrel_1(X0,sK1)
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_601]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_828,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_827]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_598,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,sK0)
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v3_relat_2(sK1)
% 1.71/1.00      | k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_596]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_830,plain,
% 1.71/1.00      ( k7_eqrel_1(sK0,sK1) = k8_eqrel_1(sK0,sK1) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_828,c_27,c_26,c_24,c_598]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1550,plain,
% 1.71/1.00      ( v1_xboole_0(k8_eqrel_1(sK0,sK1)) != iProver_top ),
% 1.71/1.00      inference(light_normalisation,[status(thm)],[c_1526,c_830]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_11,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | ~ v8_relat_2(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_640,plain,
% 1.71/1.00      ( ~ v1_partfun1(X0,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.71/1.00      | ~ v3_relat_2(X0)
% 1.71/1.00      | sK1 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_641,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | ~ v3_relat_2(sK1) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_645,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ v1_partfun1(sK1,X0) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_641,c_26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_646,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_645]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_805,plain,
% 1.71/1.00      ( m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 1.71/1.00      | sK1 != sK1
% 1.71/1.00      | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_646]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_806,plain,
% 1.71/1.00      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_805]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_643,plain,
% 1.71/1.00      ( ~ v1_partfun1(sK1,sK0)
% 1.71/1.00      | m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.71/1.00      | ~ v3_relat_2(sK1) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_641]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_808,plain,
% 1.71/1.00      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_806,c_27,c_26,c_24,c_643]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1527,plain,
% 1.71/1.00      ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.71/1.00      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1555,plain,
% 1.71/1.00      ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.71/1.00      inference(light_normalisation,[status(thm)],[c_1527,c_830]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1585,plain,
% 1.71/1.00      ( sP0_iProver_split = iProver_top ),
% 1.71/1.00      inference(forward_subsumption_resolution,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_1524,c_1550,c_1555]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1666,plain,
% 1.71/1.00      ( sP0_iProver_split ),
% 1.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1585]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_6,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | r2_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ r3_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_21,negated_conjecture,
% 1.71/1.00      ( r3_binop_1(sK0,sK2,sK3) ),
% 1.71/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_512,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | r2_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | sK3 != X0
% 1.71/1.00      | sK2 != X2
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_513,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | r2_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK2,sK0)
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_23,negated_conjecture,
% 1.71/1.00      ( m1_subset_1(sK2,sK0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_515,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | r2_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_513,c_23]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_516,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | r2_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_515]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_7,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | r1_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ r3_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_492,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | r1_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | sK3 != X0
% 1.71/1.00      | sK2 != X2
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_493,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | r1_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ m1_subset_1(sK2,sK0)
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_495,plain,
% 1.71/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | r1_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_493,c_23]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_496,plain,
% 1.71/1.00      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | r1_binop_1(sK0,sK2,sK3)
% 1.71/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_funct_1(sK3) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_495]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_5,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ r1_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ r2_binop_1(X1,X2,X0)
% 1.71/1.00      | r3_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_20,negated_conjecture,
% 1.71/1.00      ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
% 1.71/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_470,plain,
% 1.71/1.00      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ r1_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ r2_binop_1(X1,X2,X0)
% 1.71/1.00      | ~ m1_subset_1(X2,X1)
% 1.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_funct_1(X0)
% 1.71/1.00      | k9_eqrel_1(sK0,sK1,sK2) != X2
% 1.71/1.00      | k3_filter_1(sK0,sK1,sK3) != X0
% 1.71/1.00      | k8_eqrel_1(sK0,sK1) != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_471,plain,
% 1.71/1.00      ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
% 1.71/1.00      | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
% 1.71/1.00      | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
% 1.71/1.00      | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_13,plain,
% 1.71/1.00      ( ~ m2_filter_1(X0,X1,X2)
% 1.71/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_relat_1(X2)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_437,plain,
% 1.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 1.71/1.00      | ~ v1_relat_1(X2)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK3 != X0
% 1.71/1.00      | sK1 != X2
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_438,plain,
% 1.71/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 1.71/1.00      | ~ v1_relat_1(sK1)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_14,plain,
% 1.71/1.00      ( ~ m2_filter_1(X0,X1,X2)
% 1.71/1.00      | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_relat_1(X2)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_423,plain,
% 1.71/1.00      ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 1.71/1.00      | ~ v1_relat_1(X2)
% 1.71/1.00      | v1_xboole_0(X1)
% 1.71/1.00      | sK3 != X0
% 1.71/1.00      | sK1 != X2
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_424,plain,
% 1.71/1.00      ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
% 1.71/1.00      | ~ v1_relat_1(sK1)
% 1.71/1.00      | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_423]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_15,plain,
% 1.71/1.00      ( ~ m2_filter_1(X0,X1,X2)
% 1.71/1.00      | v1_funct_1(X0)
% 1.71/1.00      | ~ v1_relat_1(X2)
% 1.71/1.00      | v1_xboole_0(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_409,plain,
% 1.71/1.00      ( v1_funct_1(X0)
% 1.71/1.00      | ~ v1_relat_1(X1)
% 1.71/1.00      | v1_xboole_0(X2)
% 1.71/1.00      | sK3 != X0
% 1.71/1.00      | sK1 != X1
% 1.71/1.00      | sK0 != X2 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_410,plain,
% 1.71/1.00      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) | v1_xboole_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_412,plain,
% 1.71/1.00      ( ~ v1_relat_1(sK1) | v1_funct_1(sK3) ),
% 1.71/1.00      inference(global_propositional_subsumption,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_410,c_28]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_413,plain,
% 1.71/1.00      ( v1_funct_1(sK3) | ~ v1_relat_1(sK1) ),
% 1.71/1.00      inference(renaming,[status(thm)],[c_412]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_2,plain,
% 1.71/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.71/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_90,plain,
% 1.71/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(contradiction,plain,
% 1.71/1.00      ( $false ),
% 1.71/1.00      inference(minisat,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_1834,c_1835,c_1836,c_1807,c_1724,c_1721,c_1718,c_1666,
% 1.71/1.00                 c_516,c_496,c_471,c_438,c_424,c_413,c_90,c_23,c_24,c_28]) ).
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  ------                               Statistics
% 1.71/1.00  
% 1.71/1.00  ------ General
% 1.71/1.00  
% 1.71/1.00  abstr_ref_over_cycles:                  0
% 1.71/1.00  abstr_ref_under_cycles:                 0
% 1.71/1.00  gc_basic_clause_elim:                   0
% 1.71/1.00  forced_gc_time:                         0
% 1.71/1.00  parsing_time:                           0.011
% 1.71/1.00  unif_index_cands_time:                  0.
% 1.71/1.00  unif_index_add_time:                    0.
% 1.71/1.00  orderings_time:                         0.
% 1.71/1.00  out_proof_time:                         0.016
% 1.71/1.00  total_time:                             0.1
% 1.71/1.00  num_of_symbols:                         55
% 1.71/1.00  num_of_terms:                           1163
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing
% 1.71/1.00  
% 1.71/1.00  num_of_splits:                          1
% 1.71/1.00  num_of_split_atoms:                     1
% 1.71/1.00  num_of_reused_defs:                     0
% 1.71/1.00  num_eq_ax_congr_red:                    2
% 1.71/1.00  num_of_sem_filtered_clauses:            1
% 1.71/1.00  num_of_subtypes:                        1
% 1.71/1.00  monotx_restored_types:                  0
% 1.71/1.00  sat_num_of_epr_types:                   0
% 1.71/1.00  sat_num_of_non_cyclic_types:            0
% 1.71/1.00  sat_guarded_non_collapsed_types:        0
% 1.71/1.00  num_pure_diseq_elim:                    0
% 1.71/1.00  simp_replaced_by:                       0
% 1.71/1.00  res_preprocessed:                       128
% 1.71/1.00  prep_upred:                             0
% 1.71/1.00  prep_unflattend:                        41
% 1.71/1.00  smt_new_axioms:                         0
% 1.71/1.00  pred_elim_cands:                        7
% 1.71/1.00  pred_elim:                              6
% 1.71/1.00  pred_elim_cl:                           7
% 1.71/1.00  pred_elim_cycles:                       8
% 1.71/1.00  merged_defs:                            0
% 1.71/1.00  merged_defs_ncl:                        0
% 1.71/1.00  bin_hyper_res:                          0
% 1.71/1.00  prep_cycles:                            4
% 1.71/1.00  pred_elim_time:                         0.016
% 1.71/1.00  splitting_time:                         0.
% 1.71/1.00  sem_filter_time:                        0.
% 1.71/1.00  monotx_time:                            0.
% 1.71/1.00  subtype_inf_time:                       0.
% 1.71/1.00  
% 1.71/1.00  ------ Problem properties
% 1.71/1.00  
% 1.71/1.00  clauses:                                23
% 1.71/1.00  conjectures:                            3
% 1.71/1.00  epr:                                    3
% 1.71/1.00  horn:                                   22
% 1.71/1.00  ground:                                 14
% 1.71/1.00  unary:                                  7
% 1.71/1.00  binary:                                 3
% 1.71/1.00  lits:                                   60
% 1.71/1.00  lits_eq:                                4
% 1.71/1.00  fd_pure:                                0
% 1.71/1.00  fd_pseudo:                              0
% 1.71/1.00  fd_cond:                                0
% 1.71/1.00  fd_pseudo_cond:                         0
% 1.71/1.00  ac_symbols:                             0
% 1.71/1.00  
% 1.71/1.00  ------ Propositional Solver
% 1.71/1.00  
% 1.71/1.00  prop_solver_calls:                      24
% 1.71/1.00  prop_fast_solver_calls:                 1035
% 1.71/1.00  smt_solver_calls:                       0
% 1.71/1.00  smt_fast_solver_calls:                  0
% 1.71/1.00  prop_num_of_clauses:                    367
% 1.71/1.00  prop_preprocess_simplified:             3016
% 1.71/1.00  prop_fo_subsumed:                       34
% 1.71/1.00  prop_solver_time:                       0.
% 1.71/1.00  smt_solver_time:                        0.
% 1.71/1.00  smt_fast_solver_time:                   0.
% 1.71/1.00  prop_fast_solver_time:                  0.
% 1.71/1.00  prop_unsat_core_time:                   0.
% 1.71/1.00  
% 1.71/1.00  ------ QBF
% 1.71/1.00  
% 1.71/1.00  qbf_q_res:                              0
% 1.71/1.00  qbf_num_tautologies:                    0
% 1.71/1.00  qbf_prep_cycles:                        0
% 1.71/1.00  
% 1.71/1.00  ------ BMC1
% 1.71/1.00  
% 1.71/1.00  bmc1_current_bound:                     -1
% 1.71/1.00  bmc1_last_solved_bound:                 -1
% 1.71/1.00  bmc1_unsat_core_size:                   -1
% 1.71/1.00  bmc1_unsat_core_parents_size:           -1
% 1.71/1.00  bmc1_merge_next_fun:                    0
% 1.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation
% 1.71/1.00  
% 1.71/1.00  inst_num_of_clauses:                    71
% 1.71/1.00  inst_num_in_passive:                    21
% 1.71/1.00  inst_num_in_active:                     45
% 1.71/1.00  inst_num_in_unprocessed:                4
% 1.71/1.00  inst_num_of_loops:                      51
% 1.71/1.00  inst_num_of_learning_restarts:          0
% 1.71/1.00  inst_num_moves_active_passive:          3
% 1.71/1.00  inst_lit_activity:                      0
% 1.71/1.00  inst_lit_activity_moves:                0
% 1.71/1.00  inst_num_tautologies:                   0
% 1.71/1.00  inst_num_prop_implied:                  0
% 1.71/1.00  inst_num_existing_simplified:           0
% 1.71/1.00  inst_num_eq_res_simplified:             0
% 1.71/1.00  inst_num_child_elim:                    0
% 1.71/1.00  inst_num_of_dismatching_blockings:      0
% 1.71/1.00  inst_num_of_non_proper_insts:           20
% 1.71/1.00  inst_num_of_duplicates:                 0
% 1.71/1.00  inst_inst_num_from_inst_to_res:         0
% 1.71/1.00  inst_dismatching_checking_time:         0.
% 1.71/1.00  
% 1.71/1.00  ------ Resolution
% 1.71/1.00  
% 1.71/1.00  res_num_of_clauses:                     0
% 1.71/1.00  res_num_in_passive:                     0
% 1.71/1.00  res_num_in_active:                      0
% 1.71/1.00  res_num_of_loops:                       132
% 1.71/1.00  res_forward_subset_subsumed:            1
% 1.71/1.00  res_backward_subset_subsumed:           0
% 1.71/1.00  res_forward_subsumed:                   0
% 1.71/1.00  res_backward_subsumed:                  0
% 1.71/1.00  res_forward_subsumption_resolution:     1
% 1.71/1.00  res_backward_subsumption_resolution:    0
% 1.71/1.00  res_clause_to_clause_subsumption:       40
% 1.71/1.00  res_orphan_elimination:                 0
% 1.71/1.00  res_tautology_del:                      3
% 1.71/1.00  res_num_eq_res_simplified:              0
% 1.71/1.00  res_num_sel_changes:                    0
% 1.71/1.00  res_moves_from_active_to_pass:          0
% 1.71/1.00  
% 1.71/1.00  ------ Superposition
% 1.71/1.00  
% 1.71/1.00  sup_time_total:                         0.
% 1.71/1.00  sup_time_generating:                    0.
% 1.71/1.00  sup_time_sim_full:                      0.
% 1.71/1.00  sup_time_sim_immed:                     0.
% 1.71/1.00  
% 1.71/1.00  sup_num_of_clauses:                     23
% 1.71/1.00  sup_num_in_active:                      10
% 1.71/1.00  sup_num_in_passive:                     13
% 1.71/1.00  sup_num_of_loops:                       10
% 1.71/1.00  sup_fw_superposition:                   0
% 1.71/1.00  sup_bw_superposition:                   0
% 1.71/1.00  sup_immediate_simplified:               0
% 1.71/1.00  sup_given_eliminated:                   0
% 1.71/1.00  comparisons_done:                       0
% 1.71/1.00  comparisons_avoided:                    0
% 1.71/1.00  
% 1.71/1.00  ------ Simplifications
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  sim_fw_subset_subsumed:                 0
% 1.71/1.00  sim_bw_subset_subsumed:                 0
% 1.71/1.00  sim_fw_subsumed:                        0
% 1.71/1.00  sim_bw_subsumed:                        0
% 1.71/1.00  sim_fw_subsumption_res:                 3
% 1.71/1.00  sim_bw_subsumption_res:                 0
% 1.71/1.00  sim_tautology_del:                      0
% 1.71/1.00  sim_eq_tautology_del:                   0
% 1.71/1.00  sim_eq_res_simp:                        0
% 1.71/1.00  sim_fw_demodulated:                     0
% 1.71/1.00  sim_bw_demodulated:                     0
% 1.71/1.00  sim_light_normalised:                   2
% 1.71/1.00  sim_joinable_taut:                      0
% 1.71/1.00  sim_joinable_simp:                      0
% 1.71/1.00  sim_ac_normalised:                      0
% 1.71/1.00  sim_smt_subsumption:                    0
% 1.71/1.00  
%------------------------------------------------------------------------------
