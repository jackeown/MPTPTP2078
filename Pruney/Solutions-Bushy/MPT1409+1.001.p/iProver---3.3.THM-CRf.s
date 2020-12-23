%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1409+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  280 (4198 expanded)
%              Number of clauses        :  183 ( 959 expanded)
%              Number of leaves         :   26 (1629 expanded)
%              Depth                    :   30
%              Number of atoms          : 1322 (30061 expanded)
%              Number of equality atoms :  264 (4517 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
                  ( m1_subset_1(X3,X0)
                 => ! [X4] :
                      ( m2_filter_1(X4,X0,X1)
                     => k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) = k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
                    ( m1_subset_1(X3,X0)
                   => ! [X4] :
                        ( m2_filter_1(X4,X0,X1)
                       => k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) = k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
          & m2_filter_1(X4,X0,X1) )
     => ( k1_binop_1(k3_filter_1(X0,X1,sK9),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,sK9,X2,X3))
        & m2_filter_1(sK9,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
              & m2_filter_1(X4,X0,X1) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,sK8)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,sK8))
            & m2_filter_1(X4,X0,X1) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                  & m2_filter_1(X4,X0,X1) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,sK7),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,sK7,X3))
                & m2_filter_1(X4,X0,X1) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k1_binop_1(k3_filter_1(X0,sK6,X4),k6_eqrel_1(X0,X0,sK6,X2),k6_eqrel_1(X0,X0,sK6,X3)) != k6_eqrel_1(X0,X0,sK6,k4_binop_1(X0,X4,X2,X3))
                    & m2_filter_1(X4,X0,sK6) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK6)
        & v3_relat_2(sK6)
        & v1_partfun1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                        & m2_filter_1(X4,X0,X1) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(sK5,X1,X4),k6_eqrel_1(sK5,sK5,X1,X2),k6_eqrel_1(sK5,sK5,X1,X3)) != k6_eqrel_1(sK5,sK5,X1,k4_binop_1(sK5,X4,X2,X3))
                      & m2_filter_1(X4,sK5,X1) )
                  & m1_subset_1(X3,sK5) )
              & m1_subset_1(X2,sK5) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK5) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k6_eqrel_1(sK5,sK5,sK6,sK7),k6_eqrel_1(sK5,sK5,sK6,sK8)) != k6_eqrel_1(sK5,sK5,sK6,k4_binop_1(sK5,sK9,sK7,sK8))
    & m2_filter_1(sK9,sK5,sK6)
    & m1_subset_1(sK8,sK5)
    & m1_subset_1(sK7,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    & v8_relat_2(sK6)
    & v3_relat_2(sK6)
    & v1_partfun1(sK6,sK5)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f52,f64,f63,f62,f61,f60])).

fof(f96,plain,(
    v1_partfun1(sK6,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v3_relat_2(X1)
        & v1_relat_2(X1) )
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f46])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    v8_relat_2(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    v3_relat_2(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f99,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    m1_subset_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f57])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,(
    m1_subset_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    m2_filter_1(sK9,sK5,sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                      & v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                      & v1_funct_1(X3) )
                   => ( k3_filter_1(X0,X1,X2) = X3
                    <=> ! [X4,X5,X6,X7] :
                          ( ( r2_hidden(X7,X5)
                            & r2_hidden(X6,X4)
                            & r2_hidden(X5,k8_eqrel_1(X0,X1))
                            & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                         => k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          | ~ r2_hidden(X7,X5)
                          | ~ r2_hidden(X6,X4)
                          | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6,X7] :
          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
          & r2_hidden(X7,X5)
          & r2_hidden(X6,X4)
          & r2_hidden(X5,k8_eqrel_1(X0,X1))
          & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
     => ( k1_binop_1(X3,sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)))
        & r2_hidden(sK3(X0,X1,X2,X3),sK1(X0,X1,X2,X3))
        & r2_hidden(sK2(X0,X1,X2,X3),sK0(X0,X1,X2,X3))
        & r2_hidden(sK1(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
        & r2_hidden(sK0(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ( k1_binop_1(X3,sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)))
                        & r2_hidden(sK3(X0,X1,X2,X3),sK1(X0,X1,X2,X3))
                        & r2_hidden(sK2(X0,X1,X2,X3),sK0(X0,X1,X2,X3))
                        & r2_hidden(sK1(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
                        & r2_hidden(sK0(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f55])).

fof(f70,plain,(
    ! [X2,X0,X10,X8,X3,X1,X11,X9] :
      ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | k3_filter_1(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(X3)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    k1_binop_1(k3_filter_1(sK5,sK6,sK9),k6_eqrel_1(sK5,sK5,sK6,sK7),k6_eqrel_1(sK5,sK5,sK6,sK8)) != k6_eqrel_1(sK5,sK5,sK6,k4_binop_1(sK5,sK9,sK7,sK8)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,negated_conjecture,
    ( v1_partfun1(sK6,sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,plain,
    ( ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v1_relat_2(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | ~ v1_relat_1(X3)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_459,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_441,c_1])).

cnf(c_34,negated_conjecture,
    ( v8_relat_2(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1156,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X2)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_34])).

cnf(c_1157,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,sK6,X0))
    | ~ v1_partfun1(sK6,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_35,negated_conjecture,
    ( v3_relat_2(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(sK6,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,sK6,X0))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1157,c_35])).

cnf(c_1162,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,sK6,X0))
    | ~ v1_partfun1(sK6,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(renaming,[status(thm)],[c_1161])).

cnf(c_1407,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k6_eqrel_1(X1,X1,sK6,X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | sK6 != sK6
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1162])).

cnf(c_1408,plain,
    ( r2_hidden(X0,k6_eqrel_1(sK5,sK5,sK6,X0))
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(unflattening,[status(thm)],[c_1407])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1412,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,k6_eqrel_1(sK5,sK5,sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1408,c_33])).

cnf(c_1413,plain,
    ( r2_hidden(X0,k6_eqrel_1(sK5,sK5,sK6,X0))
    | ~ r2_hidden(X0,sK5) ),
    inference(renaming,[status(thm)],[c_1412])).

cnf(c_2432,plain,
    ( r2_hidden(X0,k6_eqrel_1(sK5,sK5,sK6,X0)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1413])).

cnf(c_2446,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_eqrel_1(X1,X2,X0,X3) = k11_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2451,plain,
    ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2923,plain,
    ( k6_eqrel_1(sK5,sK5,sK6,X0) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_2446,c_2451])).

cnf(c_3249,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2432,c_2923])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2447,plain,
    ( m1_subset_1(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,X0,X2) = k11_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1087,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,X0,X2) = k11_relat_1(X0,X2)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_1088,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK6)
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK6,X1) = k11_relat_1(sK6,X1) ),
    inference(unflattening,[status(thm)],[c_1087])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK6,X0)
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK6,X1) = k11_relat_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1088,c_35])).

cnf(c_1093,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | k9_eqrel_1(X0,sK6,X1) = k11_relat_1(sK6,X1) ),
    inference(renaming,[status(thm)],[c_1092])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | k9_eqrel_1(X1,sK6,X0) = k11_relat_1(sK6,X0)
    | sK6 != sK6
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1093])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | v1_xboole_0(sK5)
    | k9_eqrel_1(sK5,sK6,X0) = k11_relat_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(X0,sK5)
    | k9_eqrel_1(sK5,sK6,X0) = k11_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_37,c_33])).

cnf(c_2430,plain,
    ( k9_eqrel_1(sK5,sK6,X0) = k11_relat_1(sK6,X0)
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_3122,plain,
    ( k9_eqrel_1(sK5,sK6,sK7) = k11_relat_1(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_2447,c_2430])).

cnf(c_15,plain,
    ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
    | ~ v1_partfun1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_543,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_544,plain,
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
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_0,plain,
    ( ~ m1_eqrel_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_eqrel_1(k8_eqrel_1(X1,X0),X1)
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_409,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | X1 != X3
    | k8_eqrel_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_410,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_548,plain,
    ( v1_xboole_0(X1)
    | ~ v8_relat_2(X0)
    | ~ v3_relat_2(X0)
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_410])).

cnf(c_549,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(renaming,[status(thm)],[c_548])).

cnf(c_1030,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
    | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_549,c_34])).

cnf(c_1031,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK6,X1),k8_eqrel_1(X0,sK6))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK6)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | m1_subset_1(k9_eqrel_1(X0,sK6,X1),k8_eqrel_1(X0,sK6))
    | ~ m1_subset_1(X1,X0)
    | ~ v1_partfun1(sK6,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_35])).

cnf(c_1036,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(X1,X0)
    | m1_subset_1(k9_eqrel_1(X0,sK6,X1),k8_eqrel_1(X0,sK6))
    | ~ m1_subset_1(k8_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(renaming,[status(thm)],[c_1035])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_eqrel_1(X1,sK6,X0),k8_eqrel_1(X1,sK6))
    | ~ m1_subset_1(k8_eqrel_1(X1,sK6),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_zfmisc_1(X1))
    | sK6 != sK6
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1036])).

cnf(c_1474,plain,
    ( ~ m1_subset_1(X0,sK5)
    | m1_subset_1(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6))
    | ~ m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | v1_xboole_0(k1_zfmisc_1(sK5))
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_1478,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK5))
    | ~ m1_subset_1(X0,sK5)
    | m1_subset_1(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6))
    | ~ m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1474,c_37,c_33])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(X0,sK5)
    | m1_subset_1(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6))
    | ~ m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(renaming,[status(thm)],[c_1478])).

cnf(c_1931,plain,
    ( ~ m1_subset_1(X0,sK5)
    | m1_subset_1(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1479])).

cnf(c_2428,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1931])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2450,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2880,plain,
    ( r2_hidden(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_2450])).

cnf(c_38,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( v1_partfun1(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( v3_relat_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1063,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_410,c_34])).

cnf(c_1064,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK6)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k8_eqrel_1(X0,sK6)) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1065,plain,
    ( v1_partfun1(sK6,X0) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v3_relat_2(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k8_eqrel_1(X0,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_1067,plain,
    ( v1_partfun1(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) != iProver_top
    | v3_relat_2(sK6) != iProver_top
    | v1_xboole_0(k8_eqrel_1(sK5,sK6)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1932,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | v1_xboole_0(k1_zfmisc_1(sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1479])).

cnf(c_1976,plain,
    ( m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1135,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k7_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v3_relat_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_1136,plain,
    ( ~ v1_partfun1(sK6,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | m1_subset_1(k7_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ v1_partfun1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_35])).

cnf(c_1141,plain,
    ( ~ v1_partfun1(sK6,X0)
    | m1_subset_1(k7_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(renaming,[status(thm)],[c_1140])).

cnf(c_1425,plain,
    ( m1_subset_1(k7_eqrel_1(X0,sK6),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | sK6 != sK6
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1141])).

cnf(c_1426,plain,
    ( m1_subset_1(k7_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(unflattening,[status(thm)],[c_1425])).

cnf(c_1138,plain,
    ( ~ v1_partfun1(sK6,sK5)
    | m1_subset_1(k7_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ v3_relat_2(sK6) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1428,plain,
    ( m1_subset_1(k7_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_36,c_35,c_33,c_1138])).

cnf(c_2431,plain,
    ( m1_subset_1(k7_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1114,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v3_relat_2(X0)
    | k7_eqrel_1(X1,X0) = k8_eqrel_1(X1,X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_1115,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v3_relat_2(sK6)
    | k7_eqrel_1(X0,sK6) = k8_eqrel_1(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_1114])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_partfun1(sK6,X0)
    | k7_eqrel_1(X0,sK6) = k8_eqrel_1(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_35])).

cnf(c_1120,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK6) = k8_eqrel_1(X0,sK6) ),
    inference(renaming,[status(thm)],[c_1119])).

cnf(c_1436,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k7_eqrel_1(X0,sK6) = k8_eqrel_1(X0,sK6)
    | sK6 != sK6
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1120])).

cnf(c_1437,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | k7_eqrel_1(sK5,sK6) = k8_eqrel_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_1436])).

cnf(c_1117,plain,
    ( ~ v1_partfun1(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ v3_relat_2(sK6)
    | k7_eqrel_1(sK5,sK6) = k8_eqrel_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1439,plain,
    ( k7_eqrel_1(sK5,sK6) = k8_eqrel_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1437,c_36,c_35,c_33,c_1117])).

cnf(c_2472,plain,
    ( m1_subset_1(k8_eqrel_1(sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2431,c_1439])).

cnf(c_19,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2453,plain,
    ( m1_subset_1(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2875,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_2450])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2449,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3030,plain,
    ( r2_hidden(X0,k8_eqrel_1(sK5,sK6)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_2449])).

cnf(c_3970,plain,
    ( v1_xboole_0(k8_eqrel_1(sK5,sK6)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2875,c_3030])).

cnf(c_4471,plain,
    ( r2_hidden(k9_eqrel_1(sK5,sK6,X0),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2880,c_38,c_39,c_40,c_42,c_1067,c_1976,c_2472,c_3970])).

cnf(c_4480,plain,
    ( r2_hidden(k11_relat_1(sK6,sK7),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_4471])).

cnf(c_3227,plain,
    ( m1_subset_1(k11_relat_1(sK6,sK7),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK7,sK5) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_2428])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3863,plain,
    ( m1_subset_1(k11_relat_1(sK6,sK7),k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_43])).

cnf(c_3869,plain,
    ( r2_hidden(k11_relat_1(sK6,sK7),k8_eqrel_1(sK5,sK6)) = iProver_top
    | v1_xboole_0(k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3863,c_2450])).

cnf(c_4646,plain,
    ( r2_hidden(k11_relat_1(sK6,sK7),k8_eqrel_1(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4480,c_38,c_39,c_40,c_42,c_1067,c_1976,c_2472,c_3869,c_3970])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2448,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3121,plain,
    ( k9_eqrel_1(sK5,sK6,sK8) = k11_relat_1(sK6,sK8) ),
    inference(superposition,[status(thm)],[c_2448,c_2430])).

cnf(c_4479,plain,
    ( r2_hidden(k11_relat_1(sK6,sK8),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_4471])).

cnf(c_3224,plain,
    ( m1_subset_1(k11_relat_1(sK6,sK8),k8_eqrel_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_2428])).

cnf(c_44,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3854,plain,
    ( m1_subset_1(k11_relat_1(sK6,sK8),k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_44])).

cnf(c_3860,plain,
    ( r2_hidden(k11_relat_1(sK6,sK8),k8_eqrel_1(sK5,sK6)) = iProver_top
    | v1_xboole_0(k8_eqrel_1(sK5,sK6)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3854,c_2450])).

cnf(c_4639,plain,
    ( r2_hidden(k11_relat_1(sK6,sK8),k8_eqrel_1(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4479,c_38,c_39,c_40,c_42,c_1067,c_1976,c_2472,c_3860,c_3970])).

cnf(c_18,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( m2_filter_1(sK9,sK5,sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_628,plain,
    ( v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X2)
    | sK9 != X0
    | sK6 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_629,plain,
    ( v1_funct_1(sK9)
    | ~ v1_relat_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_631,plain,
    ( ~ v1_relat_1(sK6)
    | v1_funct_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_37])).

cnf(c_632,plain,
    ( v1_funct_1(sK9)
    | ~ v1_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_631])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_1(sK9)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_632])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(sK9) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_944,plain,
    ( v1_funct_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_33,c_942])).

cnf(c_17,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_642,plain,
    ( v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK9 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_643,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( ~ v1_relat_1(sK6)
    | v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_37])).

cnf(c_646,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_926,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_646])).

cnf(c_927,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_929,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_931,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_33,c_929])).

cnf(c_16,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | sK9 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_657,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ v1_relat_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_659,plain,
    ( ~ v1_relat_1(sK6)
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_37])).

cnf(c_660,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ v1_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_659])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_660])).

cnf(c_914,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_916,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_918,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_914,c_33,c_916])).

cnf(c_9,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6)
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X6,k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_filter_1(X1,X2,X0))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1)
    | k6_eqrel_1(X1,X1,X2,k1_binop_1(X0,X5,X3)) = k1_binop_1(k3_filter_1(X1,X2,X0),X6,X4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_filter_1(X1,X2,X0))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ v1_funct_1(X0)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_229,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m2_filter_1(X0,X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6)
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X6,k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1)
    | k6_eqrel_1(X1,X1,X2,k1_binop_1(X0,X5,X3)) = k1_binop_1(k3_filter_1(X1,X2,X0),X6,X4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_12,c_11,c_10])).

cnf(c_230,plain,
    ( ~ m2_filter_1(X0,X1,X2)
    | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6)
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X6,k8_eqrel_1(X1,X2))
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | v1_xboole_0(X1)
    | k6_eqrel_1(X1,X1,X2,k1_binop_1(X0,X5,X3)) = k1_binop_1(k3_filter_1(X1,X2,X0),X6,X4) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_592,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X5)
    | ~ r2_hidden(X3,k8_eqrel_1(X1,X6))
    | ~ r2_hidden(X5,k8_eqrel_1(X1,X6))
    | ~ v1_partfun1(X6,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v3_relat_2(X6)
    | ~ v8_relat_2(X6)
    | v1_xboole_0(X1)
    | k6_eqrel_1(X1,X1,X6,k1_binop_1(X0,X4,X2)) = k1_binop_1(k3_filter_1(X1,X6,X0),X5,X3)
    | sK9 != X0
    | sK6 != X6
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_30])).

cnf(c_593,plain,
    ( ~ v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | ~ v1_partfun1(sK6,sK5)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    | ~ v1_funct_1(sK9)
    | ~ v3_relat_2(sK6)
    | ~ v8_relat_2(sK6)
    | v1_xboole_0(sK5)
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_597,plain,
    ( ~ v1_funct_1(sK9)
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X0,X1)
    | ~ v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_37,c_36,c_35,c_34,c_33])).

cnf(c_598,plain,
    ( ~ v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5)))
    | ~ v1_funct_1(sK9)
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_953,plain,
    ( ~ v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5)
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | ~ v1_funct_1(sK9)
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_918,c_598])).

cnf(c_980,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | ~ v1_funct_1(sK9)
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_931,c_953])).

cnf(c_1006,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k8_eqrel_1(sK5,sK6))
    | ~ r2_hidden(X1,k8_eqrel_1(sK5,sK6))
    | k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X2,X0)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X3,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_944,c_980])).

cnf(c_2440,plain,
    ( k6_eqrel_1(sK5,sK5,sK6,k1_binop_1(sK9,X0,X1)) = k1_binop_1(k3_filter_1(sK5,sK6,sK9),X2,X3)
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X2,k8_eqrel_1(sK5,sK6)) != iProver_top
    | r2_hidden(X3,k8_eqrel_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_5819,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),X0,X1) = k11_relat_1(sK6,k1_binop_1(sK9,X2,X3))
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,k8_eqrel_1(sK5,sK6)) != iProver_top
    | r2_hidden(X0,k8_eqrel_1(sK5,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2440,c_2923])).

cnf(c_5830,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),X0,k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,X1,X2))
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,k11_relat_1(sK6,sK8)) != iProver_top
    | r2_hidden(X0,k8_eqrel_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4639,c_5819])).

cnf(c_6017,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,X0,X1))
    | r2_hidden(X1,k11_relat_1(sK6,sK8)) != iProver_top
    | r2_hidden(X0,k11_relat_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4646,c_5830])).

cnf(c_6647,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,X0,sK8))
    | r2_hidden(X0,k11_relat_1(sK6,sK7)) != iProver_top
    | r2_hidden(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_6017])).

cnf(c_2718,plain,
    ( r2_hidden(sK8,sK5)
    | ~ m1_subset_1(sK8,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2719,plain,
    ( r2_hidden(sK8,sK5) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2718])).

cnf(c_6730,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,sK7)) != iProver_top
    | k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,X0,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6647,c_38,c_44,c_2719])).

cnf(c_6731,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,X0,sK8))
    | r2_hidden(X0,k11_relat_1(sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6730])).

cnf(c_6739,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) = k11_relat_1(sK6,k1_binop_1(sK9,sK7,sK8))
    | r2_hidden(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_6731])).

cnf(c_2444,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK5),sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | k4_binop_1(X1,X0,X2,X3) = k1_binop_1(X0,X2,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2452,plain,
    ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
    | v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3730,plain,
    ( k4_binop_1(sK5,sK9,X0,X1) = k1_binop_1(sK9,X0,X1)
    | v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2444,c_2452])).

cnf(c_928,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_930,plain,
    ( v1_funct_2(sK9,k2_zfmisc_1(sK5,sK5),sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_941,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_943,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) != iProver_top
    | v1_funct_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_4913,plain,
    ( m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | k4_binop_1(sK5,sK9,X0,X1) = k1_binop_1(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_42,c_930,c_943])).

cnf(c_4914,plain,
    ( k4_binop_1(sK5,sK9,X0,X1) = k1_binop_1(sK9,X0,X1)
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4913])).

cnf(c_4924,plain,
    ( k4_binop_1(sK5,sK9,sK7,X0) = k1_binop_1(sK9,sK7,X0)
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2447,c_4914])).

cnf(c_5237,plain,
    ( k4_binop_1(sK5,sK9,sK7,sK8) = k1_binop_1(sK9,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_2448,c_4924])).

cnf(c_29,negated_conjecture,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k6_eqrel_1(sK5,sK5,sK6,sK7),k6_eqrel_1(sK5,sK5,sK6,sK8)) != k6_eqrel_1(sK5,sK5,sK6,k4_binop_1(sK5,sK9,sK7,sK8)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3051,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k6_eqrel_1(sK5,sK5,sK6,sK8)) != k6_eqrel_1(sK5,sK5,sK6,k4_binop_1(sK5,sK9,sK7,sK8)) ),
    inference(demodulation,[status(thm)],[c_2923,c_29])).

cnf(c_3052,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) != k11_relat_1(sK6,k4_binop_1(sK5,sK9,sK7,sK8)) ),
    inference(demodulation,[status(thm)],[c_3051,c_2923])).

cnf(c_5293,plain,
    ( k1_binop_1(k3_filter_1(sK5,sK6,sK9),k11_relat_1(sK6,sK7),k11_relat_1(sK6,sK8)) != k11_relat_1(sK6,k1_binop_1(sK9,sK7,sK8)) ),
    inference(demodulation,[status(thm)],[c_5237,c_3052])).

cnf(c_2721,plain,
    ( r2_hidden(sK7,sK5)
    | ~ m1_subset_1(sK7,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2722,plain,
    ( r2_hidden(sK7,sK5) = iProver_top
    | m1_subset_1(sK7,sK5) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2721])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6739,c_5293,c_2722,c_43,c_38])).


%------------------------------------------------------------------------------
