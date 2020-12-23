%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:40 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 748 expanded)
%              Number of clauses        :  101 ( 151 expanded)
%              Number of leaves         :   20 ( 273 expanded)
%              Depth                    :   16
%              Number of atoms          :  877 (5726 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f43])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK4))
        & r3_binop_1(X0,X2,sK4)
        & m2_filter_1(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f50,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    & r3_binop_1(sK1,sK3,sK4)
    & m2_filter_1(sK4,sK1,sK2)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v8_relat_2(sK2)
    & v3_relat_2(sK2)
    & v1_partfun1(sK2,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f49,f48,f47,f46])).

fof(f73,plain,(
    v1_partfun1(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    v8_relat_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    v3_relat_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(cnf_transformation,[],[f22])).

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
    inference(cnf_transformation,[],[f22])).

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
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f70,plain,(
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

fof(f78,plain,(
    m2_filter_1(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f71,plain,(
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

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f20])).

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

fof(f79,plain,(
    r3_binop_1(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f80,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1311,plain,
    ( m1_subset_1(sK0(k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_17,c_18])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(X0,k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(k8_eqrel_1(sK1,sK2))
    | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK0(k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | v1_xboole_0(k8_eqrel_1(sK1,sK2))
    | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_28,negated_conjecture,
    ( v1_partfun1(sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( v8_relat_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_681,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_7,c_26])).

cnf(c_27,negated_conjecture,
    ( v3_relat_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_685,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_27])).

cnf(c_686,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,sK2,X0))
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_685])).

cnf(c_938,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK1,sK2,X0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_28,c_686])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_942,plain,
    ( v1_funct_1(k3_filter_1(sK1,sK2,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_29,c_25])).

cnf(c_943,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(sK1,sK2,X0)) ),
    inference(renaming,[status(thm)],[c_942])).

cnf(c_1237,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | v1_funct_1(k3_filter_1(sK1,sK2,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_943])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_713,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

cnf(c_717,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_27])).

cnf(c_718,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_915,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_28,c_718])).

cnf(c_919,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_915,c_29,c_25])).

cnf(c_920,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | v1_funct_2(k3_filter_1(sK1,sK2,X0),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_919])).

cnf(c_1238,plain,
    ( v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_920])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_745,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_5,c_26])).

cnf(c_749,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_partfun1(sK2,X1)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_27])).

cnf(c_750,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK2),k8_eqrel_1(X1,sK2)),k8_eqrel_1(X1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_892,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_28,c_750])).

cnf(c_896,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_29,c_25])).

cnf(c_897,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | m1_subset_1(k3_filter_1(sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_896])).

cnf(c_1239,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_19,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r1_binop_1(X1,X3,X0)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( m2_filter_1(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_514,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,X0,sK4)
    | ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2)
    | ~ v8_relat_2(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_19,c_23])).

cnf(c_518,plain,
    ( ~ r1_binop_1(sK1,X0,sK4)
    | r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_29,c_28,c_27,c_26,c_25])).

cnf(c_519,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,X0,sK4)
    | ~ m1_subset_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_1234,plain,
    ( r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r1_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_20,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ r2_binop_1(X1,X3,X0)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_494,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,X0,sK4)
    | ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v3_relat_2(sK2)
    | ~ v8_relat_2(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_20,c_23])).

cnf(c_498,plain,
    ( ~ r2_binop_1(sK1,X0,sK4)
    | r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_29,c_28,c_27,c_26,c_25])).

cnf(c_499,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,X0),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,X0,sK4)
    | ~ m1_subset_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_1231,plain,
    ( r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_9,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_450,plain,
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
    inference(resolution,[status(thm)],[c_9,c_16])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_eqrel_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_eqrel_1(k8_eqrel_1(X1,X0),X1)
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_332,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_10,c_8])).

cnf(c_0,plain,
    ( ~ m1_eqrel_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_352,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_454,plain,
    ( v1_xboole_0(X1)
    | ~ v8_relat_2(X0)
    | ~ v3_relat_2(X0)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_332,c_352])).

cnf(c_455,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_632,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_455,c_26])).

cnf(c_636,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK2,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_27])).

cnf(c_637,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK2,X1),k8_eqrel_1(X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_28,c_637])).

cnf(c_876,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_29,c_25])).

cnf(c_877,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k9_eqrel_1(sK1,sK2,X0),k8_eqrel_1(sK1,sK2))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(renaming,[status(thm)],[c_876])).

cnf(c_1228,plain,
    ( m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( r3_binop_1(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[status(thm)],[c_3,c_22])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1007,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(sK1,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[status(thm)],[c_4,c_22])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_986,plain,
    ( ~ v1_funct_2(k3_filter_1(sK1,sK2,sK4),k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))
    | ~ r1_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ r2_binop_1(k8_eqrel_1(sK1,sK2),k9_eqrel_1(sK1,sK2,sK3),k3_filter_1(sK1,sK2,sK4))
    | ~ m1_subset_1(k9_eqrel_1(sK1,sK2,sK3),k8_eqrel_1(sK1,sK2))
    | ~ m1_subset_1(k3_filter_1(sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK1,sK2),k8_eqrel_1(sK1,sK2)),k8_eqrel_1(sK1,sK2))))
    | ~ v1_funct_1(k3_filter_1(sK1,sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_21])).

cnf(c_661,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_eqrel_1(k8_eqrel_1(X0,sK2),X0)
    | ~ v3_relat_2(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_26])).

cnf(c_665,plain,
    ( m1_eqrel_1(k8_eqrel_1(X0,sK2),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_27])).

cnf(c_666,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_eqrel_1(k8_eqrel_1(X0,sK2),X0) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_826,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k8_eqrel_1(X0,sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_666])).

cnf(c_828,plain,
    ( ~ v1_partfun1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_xboole_0(k8_eqrel_1(sK1,sK2))
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_812,plain,
    ( ~ v1_partfun1(sK2,X0)
    | m1_subset_1(k8_eqrel_1(X0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(resolution,[status(thm)],[c_10,c_666])).

cnf(c_814,plain,
    ( ~ v1_partfun1(sK2,sK1)
    | m1_subset_1(k8_eqrel_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_534,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_13,c_23])).

cnf(c_536,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_29])).

cnf(c_537,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_536])).

cnf(c_614,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(sK4) ),
    inference(resolution,[status(thm)],[c_1,c_537])).

cnf(c_616,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_12,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_547,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

cnf(c_549,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_29])).

cnf(c_550,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_549])).

cnf(c_602,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[status(thm)],[c_1,c_550])).

cnf(c_604,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_11,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_560,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_23])).

cnf(c_562,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_29])).

cnf(c_563,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_590,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[status(thm)],[c_1,c_563])).

cnf(c_592,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1311,c_1310,c_1237,c_1238,c_1239,c_1234,c_1231,c_1228,c_1017,c_1007,c_986,c_828,c_814,c_616,c_604,c_592,c_24,c_25,c_28,c_29])).


%------------------------------------------------------------------------------
