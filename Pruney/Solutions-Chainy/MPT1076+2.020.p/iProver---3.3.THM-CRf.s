%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:24 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 991 expanded)
%              Number of clauses        :  102 ( 255 expanded)
%              Number of leaves         :   17 ( 370 expanded)
%              Depth                    :   19
%              Number of atoms          :  680 (7942 expanded)
%              Number of equality atoms :  173 (1110 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f39,f38,f37,f36,f35])).

fof(f64,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1383,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1863,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_24,c_23,c_21])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(X0_51,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51) ),
    inference(subtyping,[status(esa)],[c_697])).

cnf(c_1877,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_2417,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1863,c_1877])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_715,plain,
    ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_24,c_23,c_21])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
    inference(renaming,[status(thm)],[c_715])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0_51,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) ),
    inference(subtyping,[status(esa)],[c_716])).

cnf(c_1878,plain,
    ( m1_subset_1(X0_51,sK1) != iProver_top
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_2531,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_1878])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3015,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2531,c_33])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1382,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1864,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_266,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_324,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_266,c_14])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_relat_1(X4)
    | X6 != X3
    | X4 != X2
    | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
    | k1_relat_1(X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_324])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X3)))
    | ~ v1_funct_1(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k7_partfun1(X3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_266,c_13])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k7_partfun1(X3,X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_558,c_341])).

cnf(c_1374,plain,
    ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X1_51)
    | v1_xboole_0(X1_52)
    | v1_xboole_0(k1_relat_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | k3_funct_2(k1_relat_1(X1_51),X1_52,X1_51,X0_51) = k7_partfun1(X1_52,X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_578])).

cnf(c_1872,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1374])).

cnf(c_3686,plain,
    ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1872])).

cnf(c_17,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1384,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1862,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1386,plain,
    ( ~ v1_partfun1(X0_51,X0_52)
    | ~ v4_relat_1(X0_51,X0_52)
    | ~ v1_relat_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1861,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_partfun1(X0_51,X0_52) != iProver_top
    | v4_relat_1(X0_51,X0_52) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_2607,plain,
    ( k1_relat_1(sK4) = sK0
    | v4_relat_1(sK4,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1861])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1389,plain,
    ( v4_relat_1(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2107,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_2108,plain,
    ( v4_relat_1(sK4,sK0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1856,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_2225,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1856])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1390,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2260,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_2261,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_2702,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2607,c_32,c_2108,c_2225,c_2261])).

cnf(c_3707,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3686,c_2702])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1388,plain,
    ( ~ v1_partfun1(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_xboole_0(X1_52)
    | v1_xboole_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1859,plain,
    ( v1_partfun1(X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_xboole_0(X1_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_2538,plain,
    ( v1_partfun1(sK4,sK0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1859])).

cnf(c_3875,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3707,c_26,c_31,c_34,c_2225,c_2261,c_2538])).

cnf(c_3884,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3015,c_3875])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X4)
    | X6 != X3
    | X4 != X2
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | k1_relat_1(X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_324])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X3)))
    | ~ v1_funct_1(X1)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_590,c_341])).

cnf(c_1373,plain,
    ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X1_51)
    | v1_xboole_0(k1_relat_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | k3_funct_2(k1_relat_1(X1_51),X1_52,X1_51,X0_51) = k1_funct_1(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_1873,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_3355,plain,
    ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1873])).

cnf(c_3373,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3355,c_2702])).

cnf(c_3449,plain,
    ( m1_subset_1(X0_51,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_26,c_31,c_2225,c_2261])).

cnf(c_3450,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3449])).

cnf(c_3458,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3015,c_3450])).

cnf(c_3893,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3884,c_3458])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X3,X2)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_647,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
    | sK3 != X4
    | sK0 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_648,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_652,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_25,c_24,c_23,c_21])).

cnf(c_653,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_1371,plain,
    ( ~ v1_partfun1(X0_51,sK0)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
    | ~ m1_subset_1(X1_51,sK1)
    | ~ v1_funct_1(X0_51)
    | k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51)) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_1875,plain,
    ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51))
    | v1_partfun1(X0_51,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
    | m1_subset_1(X1_51,sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_2863,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_51,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1875])).

cnf(c_2868,plain,
    ( m1_subset_1(X0_51,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_31,c_34])).

cnf(c_2869,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2868])).

cnf(c_2876,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1863,c_2869])).

cnf(c_2877,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2876,c_2417])).

cnf(c_16,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1385,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2487,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2417,c_1385])).

cnf(c_3021,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2877,c_2487])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3893,c_3021])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.50/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/1.00  
% 2.50/1.00  ------  iProver source info
% 2.50/1.00  
% 2.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/1.00  git: non_committed_changes: false
% 2.50/1.00  git: last_make_outside_of_git: false
% 2.50/1.00  
% 2.50/1.00  ------ 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options
% 2.50/1.00  
% 2.50/1.00  --out_options                           all
% 2.50/1.00  --tptp_safe_out                         true
% 2.50/1.00  --problem_path                          ""
% 2.50/1.00  --include_path                          ""
% 2.50/1.00  --clausifier                            res/vclausify_rel
% 2.50/1.00  --clausifier_options                    --mode clausify
% 2.50/1.00  --stdin                                 false
% 2.50/1.00  --stats_out                             all
% 2.50/1.00  
% 2.50/1.00  ------ General Options
% 2.50/1.00  
% 2.50/1.00  --fof                                   false
% 2.50/1.00  --time_out_real                         305.
% 2.50/1.00  --time_out_virtual                      -1.
% 2.50/1.00  --symbol_type_check                     false
% 2.50/1.00  --clausify_out                          false
% 2.50/1.00  --sig_cnt_out                           false
% 2.50/1.00  --trig_cnt_out                          false
% 2.50/1.00  --trig_cnt_out_tolerance                1.
% 2.50/1.00  --trig_cnt_out_sk_spl                   false
% 2.50/1.00  --abstr_cl_out                          false
% 2.50/1.00  
% 2.50/1.00  ------ Global Options
% 2.50/1.00  
% 2.50/1.00  --schedule                              default
% 2.50/1.00  --add_important_lit                     false
% 2.50/1.00  --prop_solver_per_cl                    1000
% 2.50/1.00  --min_unsat_core                        false
% 2.50/1.00  --soft_assumptions                      false
% 2.50/1.00  --soft_lemma_size                       3
% 2.50/1.00  --prop_impl_unit_size                   0
% 2.50/1.00  --prop_impl_unit                        []
% 2.50/1.00  --share_sel_clauses                     true
% 2.50/1.00  --reset_solvers                         false
% 2.50/1.00  --bc_imp_inh                            [conj_cone]
% 2.50/1.00  --conj_cone_tolerance                   3.
% 2.50/1.00  --extra_neg_conj                        none
% 2.50/1.00  --large_theory_mode                     true
% 2.50/1.00  --prolific_symb_bound                   200
% 2.50/1.00  --lt_threshold                          2000
% 2.50/1.00  --clause_weak_htbl                      true
% 2.50/1.00  --gc_record_bc_elim                     false
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing Options
% 2.50/1.00  
% 2.50/1.00  --preprocessing_flag                    true
% 2.50/1.00  --time_out_prep_mult                    0.1
% 2.50/1.00  --splitting_mode                        input
% 2.50/1.00  --splitting_grd                         true
% 2.50/1.00  --splitting_cvd                         false
% 2.50/1.00  --splitting_cvd_svl                     false
% 2.50/1.00  --splitting_nvd                         32
% 2.50/1.00  --sub_typing                            true
% 2.50/1.00  --prep_gs_sim                           true
% 2.50/1.00  --prep_unflatten                        true
% 2.50/1.00  --prep_res_sim                          true
% 2.50/1.00  --prep_upred                            true
% 2.50/1.00  --prep_sem_filter                       exhaustive
% 2.50/1.00  --prep_sem_filter_out                   false
% 2.50/1.00  --pred_elim                             true
% 2.50/1.00  --res_sim_input                         true
% 2.50/1.00  --eq_ax_congr_red                       true
% 2.50/1.00  --pure_diseq_elim                       true
% 2.50/1.00  --brand_transform                       false
% 2.50/1.00  --non_eq_to_eq                          false
% 2.50/1.00  --prep_def_merge                        true
% 2.50/1.00  --prep_def_merge_prop_impl              false
% 2.50/1.00  --prep_def_merge_mbd                    true
% 2.50/1.00  --prep_def_merge_tr_red                 false
% 2.50/1.00  --prep_def_merge_tr_cl                  false
% 2.50/1.00  --smt_preprocessing                     true
% 2.50/1.00  --smt_ac_axioms                         fast
% 2.50/1.00  --preprocessed_out                      false
% 2.50/1.00  --preprocessed_stats                    false
% 2.50/1.00  
% 2.50/1.00  ------ Abstraction refinement Options
% 2.50/1.00  
% 2.50/1.00  --abstr_ref                             []
% 2.50/1.00  --abstr_ref_prep                        false
% 2.50/1.00  --abstr_ref_until_sat                   false
% 2.50/1.00  --abstr_ref_sig_restrict                funpre
% 2.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.00  --abstr_ref_under                       []
% 2.50/1.00  
% 2.50/1.00  ------ SAT Options
% 2.50/1.00  
% 2.50/1.00  --sat_mode                              false
% 2.50/1.00  --sat_fm_restart_options                ""
% 2.50/1.00  --sat_gr_def                            false
% 2.50/1.00  --sat_epr_types                         true
% 2.50/1.00  --sat_non_cyclic_types                  false
% 2.50/1.00  --sat_finite_models                     false
% 2.50/1.00  --sat_fm_lemmas                         false
% 2.50/1.00  --sat_fm_prep                           false
% 2.50/1.00  --sat_fm_uc_incr                        true
% 2.50/1.00  --sat_out_model                         small
% 2.50/1.00  --sat_out_clauses                       false
% 2.50/1.00  
% 2.50/1.00  ------ QBF Options
% 2.50/1.00  
% 2.50/1.00  --qbf_mode                              false
% 2.50/1.00  --qbf_elim_univ                         false
% 2.50/1.00  --qbf_dom_inst                          none
% 2.50/1.00  --qbf_dom_pre_inst                      false
% 2.50/1.00  --qbf_sk_in                             false
% 2.50/1.00  --qbf_pred_elim                         true
% 2.50/1.00  --qbf_split                             512
% 2.50/1.00  
% 2.50/1.00  ------ BMC1 Options
% 2.50/1.00  
% 2.50/1.00  --bmc1_incremental                      false
% 2.50/1.00  --bmc1_axioms                           reachable_all
% 2.50/1.00  --bmc1_min_bound                        0
% 2.50/1.00  --bmc1_max_bound                        -1
% 2.50/1.00  --bmc1_max_bound_default                -1
% 2.50/1.00  --bmc1_symbol_reachability              true
% 2.50/1.00  --bmc1_property_lemmas                  false
% 2.50/1.00  --bmc1_k_induction                      false
% 2.50/1.00  --bmc1_non_equiv_states                 false
% 2.50/1.00  --bmc1_deadlock                         false
% 2.50/1.00  --bmc1_ucm                              false
% 2.50/1.00  --bmc1_add_unsat_core                   none
% 2.50/1.00  --bmc1_unsat_core_children              false
% 2.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.00  --bmc1_out_stat                         full
% 2.50/1.00  --bmc1_ground_init                      false
% 2.50/1.00  --bmc1_pre_inst_next_state              false
% 2.50/1.00  --bmc1_pre_inst_state                   false
% 2.50/1.00  --bmc1_pre_inst_reach_state             false
% 2.50/1.00  --bmc1_out_unsat_core                   false
% 2.50/1.00  --bmc1_aig_witness_out                  false
% 2.50/1.00  --bmc1_verbose                          false
% 2.50/1.00  --bmc1_dump_clauses_tptp                false
% 2.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.00  --bmc1_dump_file                        -
% 2.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.00  --bmc1_ucm_extend_mode                  1
% 2.50/1.00  --bmc1_ucm_init_mode                    2
% 2.50/1.00  --bmc1_ucm_cone_mode                    none
% 2.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.00  --bmc1_ucm_relax_model                  4
% 2.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.00  --bmc1_ucm_layered_model                none
% 2.50/1.00  --bmc1_ucm_max_lemma_size               10
% 2.50/1.00  
% 2.50/1.00  ------ AIG Options
% 2.50/1.00  
% 2.50/1.00  --aig_mode                              false
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation Options
% 2.50/1.00  
% 2.50/1.00  --instantiation_flag                    true
% 2.50/1.00  --inst_sos_flag                         false
% 2.50/1.00  --inst_sos_phase                        true
% 2.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel_side                     num_symb
% 2.50/1.00  --inst_solver_per_active                1400
% 2.50/1.00  --inst_solver_calls_frac                1.
% 2.50/1.00  --inst_passive_queue_type               priority_queues
% 2.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.00  --inst_passive_queues_freq              [25;2]
% 2.50/1.00  --inst_dismatching                      true
% 2.50/1.00  --inst_eager_unprocessed_to_passive     true
% 2.50/1.00  --inst_prop_sim_given                   true
% 2.50/1.00  --inst_prop_sim_new                     false
% 2.50/1.00  --inst_subs_new                         false
% 2.50/1.00  --inst_eq_res_simp                      false
% 2.50/1.00  --inst_subs_given                       false
% 2.50/1.00  --inst_orphan_elimination               true
% 2.50/1.00  --inst_learning_loop_flag               true
% 2.50/1.00  --inst_learning_start                   3000
% 2.50/1.00  --inst_learning_factor                  2
% 2.50/1.00  --inst_start_prop_sim_after_learn       3
% 2.50/1.00  --inst_sel_renew                        solver
% 2.50/1.00  --inst_lit_activity_flag                true
% 2.50/1.00  --inst_restr_to_given                   false
% 2.50/1.00  --inst_activity_threshold               500
% 2.50/1.00  --inst_out_proof                        true
% 2.50/1.00  
% 2.50/1.00  ------ Resolution Options
% 2.50/1.00  
% 2.50/1.00  --resolution_flag                       true
% 2.50/1.00  --res_lit_sel                           adaptive
% 2.50/1.00  --res_lit_sel_side                      none
% 2.50/1.00  --res_ordering                          kbo
% 2.50/1.00  --res_to_prop_solver                    active
% 2.50/1.00  --res_prop_simpl_new                    false
% 2.50/1.00  --res_prop_simpl_given                  true
% 2.50/1.00  --res_passive_queue_type                priority_queues
% 2.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.00  --res_passive_queues_freq               [15;5]
% 2.50/1.00  --res_forward_subs                      full
% 2.50/1.00  --res_backward_subs                     full
% 2.50/1.00  --res_forward_subs_resolution           true
% 2.50/1.00  --res_backward_subs_resolution          true
% 2.50/1.00  --res_orphan_elimination                true
% 2.50/1.00  --res_time_limit                        2.
% 2.50/1.00  --res_out_proof                         true
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Options
% 2.50/1.00  
% 2.50/1.00  --superposition_flag                    true
% 2.50/1.00  --sup_passive_queue_type                priority_queues
% 2.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.00  --demod_completeness_check              fast
% 2.50/1.00  --demod_use_ground                      true
% 2.50/1.00  --sup_to_prop_solver                    passive
% 2.50/1.00  --sup_prop_simpl_new                    true
% 2.50/1.00  --sup_prop_simpl_given                  true
% 2.50/1.00  --sup_fun_splitting                     false
% 2.50/1.00  --sup_smt_interval                      50000
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Simplification Setup
% 2.50/1.00  
% 2.50/1.00  --sup_indices_passive                   []
% 2.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_full_bw                           [BwDemod]
% 2.50/1.00  --sup_immed_triv                        [TrivRules]
% 2.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_immed_bw_main                     []
% 2.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  
% 2.50/1.00  ------ Combination Options
% 2.50/1.00  
% 2.50/1.00  --comb_res_mult                         3
% 2.50/1.00  --comb_sup_mult                         2
% 2.50/1.00  --comb_inst_mult                        10
% 2.50/1.00  
% 2.50/1.00  ------ Debug Options
% 2.50/1.00  
% 2.50/1.00  --dbg_backtrace                         false
% 2.50/1.00  --dbg_dump_prop_clauses                 false
% 2.50/1.00  --dbg_dump_prop_clauses_file            -
% 2.50/1.00  --dbg_out_stat                          false
% 2.50/1.00  ------ Parsing...
% 2.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/1.00  ------ Proving...
% 2.50/1.00  ------ Problem Properties 
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  clauses                                 24
% 2.50/1.00  conjectures                             9
% 2.50/1.00  EPR                                     6
% 2.50/1.00  Horn                                    20
% 2.50/1.00  unary                                   10
% 2.50/1.00  binary                                  4
% 2.50/1.00  lits                                    70
% 2.50/1.00  lits eq                                 8
% 2.50/1.00  fd_pure                                 0
% 2.50/1.00  fd_pseudo                               0
% 2.50/1.00  fd_cond                                 0
% 2.50/1.00  fd_pseudo_cond                          1
% 2.50/1.00  AC symbols                              0
% 2.50/1.00  
% 2.50/1.00  ------ Schedule dynamic 5 is on 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  ------ 
% 2.50/1.00  Current options:
% 2.50/1.00  ------ 
% 2.50/1.00  
% 2.50/1.00  ------ Input Options
% 2.50/1.00  
% 2.50/1.00  --out_options                           all
% 2.50/1.00  --tptp_safe_out                         true
% 2.50/1.00  --problem_path                          ""
% 2.50/1.00  --include_path                          ""
% 2.50/1.00  --clausifier                            res/vclausify_rel
% 2.50/1.00  --clausifier_options                    --mode clausify
% 2.50/1.00  --stdin                                 false
% 2.50/1.00  --stats_out                             all
% 2.50/1.00  
% 2.50/1.00  ------ General Options
% 2.50/1.00  
% 2.50/1.00  --fof                                   false
% 2.50/1.00  --time_out_real                         305.
% 2.50/1.00  --time_out_virtual                      -1.
% 2.50/1.00  --symbol_type_check                     false
% 2.50/1.00  --clausify_out                          false
% 2.50/1.00  --sig_cnt_out                           false
% 2.50/1.00  --trig_cnt_out                          false
% 2.50/1.00  --trig_cnt_out_tolerance                1.
% 2.50/1.00  --trig_cnt_out_sk_spl                   false
% 2.50/1.00  --abstr_cl_out                          false
% 2.50/1.00  
% 2.50/1.00  ------ Global Options
% 2.50/1.00  
% 2.50/1.00  --schedule                              default
% 2.50/1.00  --add_important_lit                     false
% 2.50/1.00  --prop_solver_per_cl                    1000
% 2.50/1.00  --min_unsat_core                        false
% 2.50/1.00  --soft_assumptions                      false
% 2.50/1.00  --soft_lemma_size                       3
% 2.50/1.00  --prop_impl_unit_size                   0
% 2.50/1.00  --prop_impl_unit                        []
% 2.50/1.00  --share_sel_clauses                     true
% 2.50/1.00  --reset_solvers                         false
% 2.50/1.00  --bc_imp_inh                            [conj_cone]
% 2.50/1.00  --conj_cone_tolerance                   3.
% 2.50/1.00  --extra_neg_conj                        none
% 2.50/1.00  --large_theory_mode                     true
% 2.50/1.00  --prolific_symb_bound                   200
% 2.50/1.00  --lt_threshold                          2000
% 2.50/1.00  --clause_weak_htbl                      true
% 2.50/1.00  --gc_record_bc_elim                     false
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing Options
% 2.50/1.00  
% 2.50/1.00  --preprocessing_flag                    true
% 2.50/1.00  --time_out_prep_mult                    0.1
% 2.50/1.00  --splitting_mode                        input
% 2.50/1.00  --splitting_grd                         true
% 2.50/1.00  --splitting_cvd                         false
% 2.50/1.00  --splitting_cvd_svl                     false
% 2.50/1.00  --splitting_nvd                         32
% 2.50/1.00  --sub_typing                            true
% 2.50/1.00  --prep_gs_sim                           true
% 2.50/1.00  --prep_unflatten                        true
% 2.50/1.00  --prep_res_sim                          true
% 2.50/1.00  --prep_upred                            true
% 2.50/1.00  --prep_sem_filter                       exhaustive
% 2.50/1.00  --prep_sem_filter_out                   false
% 2.50/1.00  --pred_elim                             true
% 2.50/1.00  --res_sim_input                         true
% 2.50/1.00  --eq_ax_congr_red                       true
% 2.50/1.00  --pure_diseq_elim                       true
% 2.50/1.00  --brand_transform                       false
% 2.50/1.00  --non_eq_to_eq                          false
% 2.50/1.00  --prep_def_merge                        true
% 2.50/1.00  --prep_def_merge_prop_impl              false
% 2.50/1.00  --prep_def_merge_mbd                    true
% 2.50/1.00  --prep_def_merge_tr_red                 false
% 2.50/1.00  --prep_def_merge_tr_cl                  false
% 2.50/1.00  --smt_preprocessing                     true
% 2.50/1.00  --smt_ac_axioms                         fast
% 2.50/1.00  --preprocessed_out                      false
% 2.50/1.00  --preprocessed_stats                    false
% 2.50/1.00  
% 2.50/1.00  ------ Abstraction refinement Options
% 2.50/1.00  
% 2.50/1.00  --abstr_ref                             []
% 2.50/1.00  --abstr_ref_prep                        false
% 2.50/1.00  --abstr_ref_until_sat                   false
% 2.50/1.00  --abstr_ref_sig_restrict                funpre
% 2.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.00  --abstr_ref_under                       []
% 2.50/1.00  
% 2.50/1.00  ------ SAT Options
% 2.50/1.00  
% 2.50/1.00  --sat_mode                              false
% 2.50/1.00  --sat_fm_restart_options                ""
% 2.50/1.00  --sat_gr_def                            false
% 2.50/1.00  --sat_epr_types                         true
% 2.50/1.00  --sat_non_cyclic_types                  false
% 2.50/1.00  --sat_finite_models                     false
% 2.50/1.00  --sat_fm_lemmas                         false
% 2.50/1.00  --sat_fm_prep                           false
% 2.50/1.00  --sat_fm_uc_incr                        true
% 2.50/1.00  --sat_out_model                         small
% 2.50/1.00  --sat_out_clauses                       false
% 2.50/1.00  
% 2.50/1.00  ------ QBF Options
% 2.50/1.00  
% 2.50/1.00  --qbf_mode                              false
% 2.50/1.00  --qbf_elim_univ                         false
% 2.50/1.00  --qbf_dom_inst                          none
% 2.50/1.00  --qbf_dom_pre_inst                      false
% 2.50/1.00  --qbf_sk_in                             false
% 2.50/1.00  --qbf_pred_elim                         true
% 2.50/1.00  --qbf_split                             512
% 2.50/1.00  
% 2.50/1.00  ------ BMC1 Options
% 2.50/1.00  
% 2.50/1.00  --bmc1_incremental                      false
% 2.50/1.00  --bmc1_axioms                           reachable_all
% 2.50/1.00  --bmc1_min_bound                        0
% 2.50/1.00  --bmc1_max_bound                        -1
% 2.50/1.00  --bmc1_max_bound_default                -1
% 2.50/1.00  --bmc1_symbol_reachability              true
% 2.50/1.00  --bmc1_property_lemmas                  false
% 2.50/1.00  --bmc1_k_induction                      false
% 2.50/1.00  --bmc1_non_equiv_states                 false
% 2.50/1.00  --bmc1_deadlock                         false
% 2.50/1.00  --bmc1_ucm                              false
% 2.50/1.00  --bmc1_add_unsat_core                   none
% 2.50/1.00  --bmc1_unsat_core_children              false
% 2.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.00  --bmc1_out_stat                         full
% 2.50/1.00  --bmc1_ground_init                      false
% 2.50/1.00  --bmc1_pre_inst_next_state              false
% 2.50/1.00  --bmc1_pre_inst_state                   false
% 2.50/1.00  --bmc1_pre_inst_reach_state             false
% 2.50/1.00  --bmc1_out_unsat_core                   false
% 2.50/1.00  --bmc1_aig_witness_out                  false
% 2.50/1.00  --bmc1_verbose                          false
% 2.50/1.00  --bmc1_dump_clauses_tptp                false
% 2.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.00  --bmc1_dump_file                        -
% 2.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.00  --bmc1_ucm_extend_mode                  1
% 2.50/1.00  --bmc1_ucm_init_mode                    2
% 2.50/1.00  --bmc1_ucm_cone_mode                    none
% 2.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.00  --bmc1_ucm_relax_model                  4
% 2.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.00  --bmc1_ucm_layered_model                none
% 2.50/1.00  --bmc1_ucm_max_lemma_size               10
% 2.50/1.00  
% 2.50/1.00  ------ AIG Options
% 2.50/1.00  
% 2.50/1.00  --aig_mode                              false
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation Options
% 2.50/1.00  
% 2.50/1.00  --instantiation_flag                    true
% 2.50/1.00  --inst_sos_flag                         false
% 2.50/1.00  --inst_sos_phase                        true
% 2.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.00  --inst_lit_sel_side                     none
% 2.50/1.00  --inst_solver_per_active                1400
% 2.50/1.00  --inst_solver_calls_frac                1.
% 2.50/1.00  --inst_passive_queue_type               priority_queues
% 2.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.00  --inst_passive_queues_freq              [25;2]
% 2.50/1.00  --inst_dismatching                      true
% 2.50/1.00  --inst_eager_unprocessed_to_passive     true
% 2.50/1.00  --inst_prop_sim_given                   true
% 2.50/1.00  --inst_prop_sim_new                     false
% 2.50/1.00  --inst_subs_new                         false
% 2.50/1.00  --inst_eq_res_simp                      false
% 2.50/1.00  --inst_subs_given                       false
% 2.50/1.00  --inst_orphan_elimination               true
% 2.50/1.00  --inst_learning_loop_flag               true
% 2.50/1.00  --inst_learning_start                   3000
% 2.50/1.00  --inst_learning_factor                  2
% 2.50/1.00  --inst_start_prop_sim_after_learn       3
% 2.50/1.00  --inst_sel_renew                        solver
% 2.50/1.00  --inst_lit_activity_flag                true
% 2.50/1.00  --inst_restr_to_given                   false
% 2.50/1.00  --inst_activity_threshold               500
% 2.50/1.00  --inst_out_proof                        true
% 2.50/1.00  
% 2.50/1.00  ------ Resolution Options
% 2.50/1.00  
% 2.50/1.00  --resolution_flag                       false
% 2.50/1.00  --res_lit_sel                           adaptive
% 2.50/1.00  --res_lit_sel_side                      none
% 2.50/1.00  --res_ordering                          kbo
% 2.50/1.00  --res_to_prop_solver                    active
% 2.50/1.00  --res_prop_simpl_new                    false
% 2.50/1.00  --res_prop_simpl_given                  true
% 2.50/1.00  --res_passive_queue_type                priority_queues
% 2.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.00  --res_passive_queues_freq               [15;5]
% 2.50/1.00  --res_forward_subs                      full
% 2.50/1.00  --res_backward_subs                     full
% 2.50/1.00  --res_forward_subs_resolution           true
% 2.50/1.00  --res_backward_subs_resolution          true
% 2.50/1.00  --res_orphan_elimination                true
% 2.50/1.00  --res_time_limit                        2.
% 2.50/1.00  --res_out_proof                         true
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Options
% 2.50/1.00  
% 2.50/1.00  --superposition_flag                    true
% 2.50/1.00  --sup_passive_queue_type                priority_queues
% 2.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.00  --demod_completeness_check              fast
% 2.50/1.00  --demod_use_ground                      true
% 2.50/1.00  --sup_to_prop_solver                    passive
% 2.50/1.00  --sup_prop_simpl_new                    true
% 2.50/1.00  --sup_prop_simpl_given                  true
% 2.50/1.00  --sup_fun_splitting                     false
% 2.50/1.00  --sup_smt_interval                      50000
% 2.50/1.00  
% 2.50/1.00  ------ Superposition Simplification Setup
% 2.50/1.00  
% 2.50/1.00  --sup_indices_passive                   []
% 2.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_full_bw                           [BwDemod]
% 2.50/1.00  --sup_immed_triv                        [TrivRules]
% 2.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_immed_bw_main                     []
% 2.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.00  
% 2.50/1.00  ------ Combination Options
% 2.50/1.00  
% 2.50/1.00  --comb_res_mult                         3
% 2.50/1.00  --comb_sup_mult                         2
% 2.50/1.00  --comb_inst_mult                        10
% 2.50/1.00  
% 2.50/1.00  ------ Debug Options
% 2.50/1.00  
% 2.50/1.00  --dbg_backtrace                         false
% 2.50/1.00  --dbg_dump_prop_clauses                 false
% 2.50/1.00  --dbg_dump_prop_clauses_file            -
% 2.50/1.00  --dbg_out_stat                          false
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  ------ Proving...
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  % SZS status Theorem for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  fof(f12,conjecture,(
% 2.50/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f13,negated_conjecture,(
% 2.50/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.50/1.00    inference(negated_conjecture,[],[f12])).
% 2.50/1.00  
% 2.50/1.00  fof(f31,plain,(
% 2.50/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.50/1.00    inference(ennf_transformation,[],[f13])).
% 2.50/1.00  
% 2.50/1.00  fof(f32,plain,(
% 2.50/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.50/1.00    inference(flattening,[],[f31])).
% 2.50/1.00  
% 2.50/1.00  fof(f39,plain,(
% 2.50/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f38,plain,(
% 2.50/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f37,plain,(
% 2.50/1.00    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f36,plain,(
% 2.50/1.00    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f35,plain,(
% 2.50/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.50/1.00    introduced(choice_axiom,[])).
% 2.50/1.00  
% 2.50/1.00  fof(f40,plain,(
% 2.50/1.00    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f39,f38,f37,f36,f35])).
% 2.50/1.00  
% 2.50/1.00  fof(f64,plain,(
% 2.50/1.00    m1_subset_1(sK5,sK1)),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f8,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f23,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.50/1.00    inference(ennf_transformation,[],[f8])).
% 2.50/1.00  
% 2.50/1.00  fof(f24,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.50/1.00    inference(flattening,[],[f23])).
% 2.50/1.00  
% 2.50/1.00  fof(f51,plain,(
% 2.50/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f24])).
% 2.50/1.00  
% 2.50/1.00  fof(f60,plain,(
% 2.50/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f58,plain,(
% 2.50/1.00    ~v1_xboole_0(sK1)),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f59,plain,(
% 2.50/1.00    v1_funct_1(sK3)),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f61,plain,(
% 2.50/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f7,axiom,(
% 2.50/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 2.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f21,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.50/1.00    inference(ennf_transformation,[],[f7])).
% 2.50/1.00  
% 2.50/1.00  fof(f22,plain,(
% 2.50/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.50/1.00    inference(flattening,[],[f21])).
% 2.50/1.00  
% 2.50/1.00  fof(f50,plain,(
% 2.50/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.50/1.00    inference(cnf_transformation,[],[f22])).
% 2.50/1.00  
% 2.50/1.00  fof(f63,plain,(
% 2.50/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.50/1.00    inference(cnf_transformation,[],[f40])).
% 2.50/1.00  
% 2.50/1.00  fof(f9,axiom,(
% 2.50/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 2.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.00  
% 2.50/1.00  fof(f25,plain,(
% 2.50/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.50/1.00    inference(ennf_transformation,[],[f9])).
% 2.50/1.00  
% 2.50/1.00  fof(f26,plain,(
% 2.50/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.50/1.00    inference(flattening,[],[f25])).
% 2.50/1.00  
% 2.50/1.00  fof(f52,plain,(
% 2.50/1.01    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f26])).
% 2.50/1.01  
% 2.50/1.01  fof(f4,axiom,(
% 2.50/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f16,plain,(
% 2.50/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/1.01    inference(ennf_transformation,[],[f4])).
% 2.50/1.01  
% 2.50/1.01  fof(f46,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/1.01    inference(cnf_transformation,[],[f16])).
% 2.50/1.01  
% 2.50/1.01  fof(f2,axiom,(
% 2.50/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f15,plain,(
% 2.50/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.50/1.01    inference(ennf_transformation,[],[f2])).
% 2.50/1.01  
% 2.50/1.01  fof(f33,plain,(
% 2.50/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.50/1.01    inference(nnf_transformation,[],[f15])).
% 2.50/1.01  
% 2.50/1.01  fof(f42,plain,(
% 2.50/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f33])).
% 2.50/1.01  
% 2.50/1.01  fof(f11,axiom,(
% 2.50/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f29,plain,(
% 2.50/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.50/1.01    inference(ennf_transformation,[],[f11])).
% 2.50/1.01  
% 2.50/1.01  fof(f30,plain,(
% 2.50/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.50/1.01    inference(flattening,[],[f29])).
% 2.50/1.01  
% 2.50/1.01  fof(f55,plain,(
% 2.50/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f30])).
% 2.50/1.01  
% 2.50/1.01  fof(f56,plain,(
% 2.50/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f30])).
% 2.50/1.01  
% 2.50/1.01  fof(f65,plain,(
% 2.50/1.01    v1_partfun1(sK4,sK0)),
% 2.50/1.01    inference(cnf_transformation,[],[f40])).
% 2.50/1.01  
% 2.50/1.01  fof(f6,axiom,(
% 2.50/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f19,plain,(
% 2.50/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.50/1.01    inference(ennf_transformation,[],[f6])).
% 2.50/1.01  
% 2.50/1.01  fof(f20,plain,(
% 2.50/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.50/1.01    inference(flattening,[],[f19])).
% 2.50/1.01  
% 2.50/1.01  fof(f34,plain,(
% 2.50/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.50/1.01    inference(nnf_transformation,[],[f20])).
% 2.50/1.01  
% 2.50/1.01  fof(f48,plain,(
% 2.50/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f34])).
% 2.50/1.01  
% 2.50/1.01  fof(f45,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/1.01    inference(cnf_transformation,[],[f16])).
% 2.50/1.01  
% 2.50/1.01  fof(f1,axiom,(
% 2.50/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f14,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.50/1.01    inference(ennf_transformation,[],[f1])).
% 2.50/1.01  
% 2.50/1.01  fof(f41,plain,(
% 2.50/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f14])).
% 2.50/1.01  
% 2.50/1.01  fof(f3,axiom,(
% 2.50/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f44,plain,(
% 2.50/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.50/1.01    inference(cnf_transformation,[],[f3])).
% 2.50/1.01  
% 2.50/1.01  fof(f57,plain,(
% 2.50/1.01    ~v1_xboole_0(sK0)),
% 2.50/1.01    inference(cnf_transformation,[],[f40])).
% 2.50/1.01  
% 2.50/1.01  fof(f62,plain,(
% 2.50/1.01    v1_funct_1(sK4)),
% 2.50/1.01    inference(cnf_transformation,[],[f40])).
% 2.50/1.01  
% 2.50/1.01  fof(f5,axiom,(
% 2.50/1.01    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f17,plain,(
% 2.50/1.01    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f5])).
% 2.50/1.01  
% 2.50/1.01  fof(f18,plain,(
% 2.50/1.01    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.50/1.01    inference(flattening,[],[f17])).
% 2.50/1.01  
% 2.50/1.01  fof(f47,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f18])).
% 2.50/1.01  
% 2.50/1.01  fof(f10,axiom,(
% 2.50/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.50/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f27,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.50/1.01    inference(ennf_transformation,[],[f10])).
% 2.50/1.01  
% 2.50/1.01  fof(f28,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.50/1.01    inference(flattening,[],[f27])).
% 2.50/1.01  
% 2.50/1.01  fof(f53,plain,(
% 2.50/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f28])).
% 2.50/1.01  
% 2.50/1.01  fof(f66,plain,(
% 2.50/1.01    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.50/1.01    inference(cnf_transformation,[],[f40])).
% 2.50/1.01  
% 2.50/1.01  cnf(c_18,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK5,sK1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1383,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK5,sK1) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1863,plain,
% 2.50/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_10,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/1.01      | ~ m1_subset_1(X3,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_22,negated_conjecture,
% 2.50/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_692,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.50/1.01      | ~ v1_funct_1(X2)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.50/1.01      | sK3 != X2
% 2.50/1.01      | sK0 != X3
% 2.50/1.01      | sK1 != X1 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_693,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,sK1)
% 2.50/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.50/1.01      | ~ v1_funct_1(sK3)
% 2.50/1.01      | v1_xboole_0(sK1)
% 2.50/1.01      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_692]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_24,negated_conjecture,
% 2.50/1.01      ( ~ v1_xboole_0(sK1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_23,negated_conjecture,
% 2.50/1.01      ( v1_funct_1(sK3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_21,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_697,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,sK1)
% 2.50/1.01      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_693,c_24,c_23,c_21]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1369,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_51,sK1)
% 2.50/1.01      | k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_697]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1877,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2417,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1863,c_1877]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_9,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/1.01      | ~ m1_subset_1(X3,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v1_xboole_0(X1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_710,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.50/1.01      | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
% 2.50/1.01      | ~ v1_funct_1(X2)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | sK3 != X2
% 2.50/1.01      | sK0 != X3
% 2.50/1.01      | sK1 != X1 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_711,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,sK1)
% 2.50/1.01      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
% 2.50/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.50/1.01      | ~ v1_funct_1(sK3)
% 2.50/1.01      | v1_xboole_0(sK1) ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_710]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_715,plain,
% 2.50/1.01      ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
% 2.50/1.01      | ~ m1_subset_1(X0,sK1) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_711,c_24,c_23,c_21]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_716,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,sK1)
% 2.50/1.01      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_715]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1368,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_51,sK1)
% 2.50/1.01      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_716]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1878,plain,
% 2.50/1.01      ( m1_subset_1(X0_51,sK1) != iProver_top
% 2.50/1.01      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1368]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2531,plain,
% 2.50/1.01      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 2.50/1.01      | m1_subset_1(sK5,sK1) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_2417,c_1878]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_33,plain,
% 2.50/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3015,plain,
% 2.50/1.01      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_2531,c_33]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_19,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1382,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1864,plain,
% 2.50/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_11,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/1.01      | ~ m1_subset_1(X3,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v1_xboole_0(X2)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4,plain,
% 2.50/1.01      ( v5_relat_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2,plain,
% 2.50/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 2.50/1.01      | ~ v5_relat_1(X0,X1)
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_266,plain,
% 2.50/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_14,plain,
% 2.50/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.50/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_324,plain,
% 2.50/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(resolution,[status(thm)],[c_266,c_14]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_557,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.50/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 2.50/1.01      | ~ v1_funct_1(X2)
% 2.50/1.01      | ~ v1_funct_1(X4)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | v1_xboole_0(X3)
% 2.50/1.01      | ~ v1_relat_1(X4)
% 2.50/1.01      | X6 != X3
% 2.50/1.01      | X4 != X2
% 2.50/1.01      | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
% 2.50/1.01      | k1_relat_1(X4) != X1 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_324]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_558,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X3)))
% 2.50/1.01      | ~ v1_funct_1(X1)
% 2.50/1.01      | v1_xboole_0(X3)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1))
% 2.50/1.01      | ~ v1_relat_1(X1)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k7_partfun1(X3,X1,X0) ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_13,plain,
% 2.50/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.50/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_341,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_relat_1(X0) ),
% 2.50/1.01      inference(resolution,[status(thm)],[c_266,c_13]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_578,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.50/1.01      | ~ v1_funct_1(X1)
% 2.50/1.01      | v1_xboole_0(X3)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1))
% 2.50/1.01      | ~ v1_relat_1(X1)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k7_partfun1(X3,X1,X0) ),
% 2.50/1.01      inference(forward_subsumption_resolution,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_558,c_341]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1374,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
% 2.50/1.01      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.50/1.01      | ~ v1_funct_1(X1_51)
% 2.50/1.01      | v1_xboole_0(X1_52)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1_51))
% 2.50/1.01      | ~ v1_relat_1(X1_51)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1_51),X1_52,X1_51,X0_51) = k7_partfun1(X1_52,X1_51,X0_51) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_578]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1872,plain,
% 2.50/1.01      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
% 2.50/1.01      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.50/1.01      | v1_xboole_0(X0_52) = iProver_top
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 2.50/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1374]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3686,plain,
% 2.50/1.01      ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
% 2.50/1.01      | v1_funct_1(sK4) != iProver_top
% 2.50/1.01      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 2.50/1.01      | v1_xboole_0(sK2) = iProver_top
% 2.50/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1864,c_1872]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_17,negated_conjecture,
% 2.50/1.01      ( v1_partfun1(sK4,sK0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1384,negated_conjecture,
% 2.50/1.01      ( v1_partfun1(sK4,sK0) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1862,plain,
% 2.50/1.01      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_8,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0,X1)
% 2.50/1.01      | ~ v4_relat_1(X0,X1)
% 2.50/1.01      | ~ v1_relat_1(X0)
% 2.50/1.01      | k1_relat_1(X0) = X1 ),
% 2.50/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1386,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0_51,X0_52)
% 2.50/1.01      | ~ v4_relat_1(X0_51,X0_52)
% 2.50/1.01      | ~ v1_relat_1(X0_51)
% 2.50/1.01      | k1_relat_1(X0_51) = X0_52 ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1861,plain,
% 2.50/1.01      ( k1_relat_1(X0_51) = X0_52
% 2.50/1.01      | v1_partfun1(X0_51,X0_52) != iProver_top
% 2.50/1.01      | v4_relat_1(X0_51,X0_52) != iProver_top
% 2.50/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2607,plain,
% 2.50/1.01      ( k1_relat_1(sK4) = sK0
% 2.50/1.01      | v4_relat_1(sK4,sK0) != iProver_top
% 2.50/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1862,c_1861]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_32,plain,
% 2.50/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5,plain,
% 2.50/1.01      ( v4_relat_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1389,plain,
% 2.50/1.01      ( v4_relat_1(X0_51,X0_52)
% 2.50/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2107,plain,
% 2.50/1.01      ( v4_relat_1(sK4,sK0)
% 2.50/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.50/1.01      inference(instantiation,[status(thm)],[c_1389]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2108,plain,
% 2.50/1.01      ( v4_relat_1(sK4,sK0) = iProver_top
% 2.50/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_0,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/1.01      | ~ v1_relat_1(X1)
% 2.50/1.01      | v1_relat_1(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1391,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.50/1.01      | ~ v1_relat_1(X1_51)
% 2.50/1.01      | v1_relat_1(X0_51) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1856,plain,
% 2.50/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 2.50/1.01      | v1_relat_1(X1_51) != iProver_top
% 2.50/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2225,plain,
% 2.50/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.50/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1864,c_1856]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3,plain,
% 2.50/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1390,plain,
% 2.50/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2260,plain,
% 2.50/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.50/1.01      inference(instantiation,[status(thm)],[c_1390]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2261,plain,
% 2.50/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2260]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2702,plain,
% 2.50/1.01      ( k1_relat_1(sK4) = sK0 ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_2607,c_32,c_2108,c_2225,c_2261]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3707,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,sK0) != iProver_top
% 2.50/1.01      | v1_funct_1(sK4) != iProver_top
% 2.50/1.01      | v1_xboole_0(sK0) = iProver_top
% 2.50/1.01      | v1_xboole_0(sK2) = iProver_top
% 2.50/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_3686,c_2702]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_25,negated_conjecture,
% 2.50/1.01      ( ~ v1_xboole_0(sK0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_26,plain,
% 2.50/1.01      ( v1_xboole_0(sK0) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_20,negated_conjecture,
% 2.50/1.01      ( v1_funct_1(sK4) ),
% 2.50/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_31,plain,
% 2.50/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_34,plain,
% 2.50/1.01      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | ~ v1_xboole_0(X2)
% 2.50/1.01      | v1_xboole_0(X1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1388,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0_51,X0_52)
% 2.50/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.50/1.01      | ~ v1_xboole_0(X1_52)
% 2.50/1.01      | v1_xboole_0(X0_52) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1859,plain,
% 2.50/1.01      ( v1_partfun1(X0_51,X0_52) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.50/1.01      | v1_xboole_0(X1_52) != iProver_top
% 2.50/1.01      | v1_xboole_0(X0_52) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2538,plain,
% 2.50/1.01      ( v1_partfun1(sK4,sK0) != iProver_top
% 2.50/1.01      | v1_xboole_0(sK0) = iProver_top
% 2.50/1.01      | v1_xboole_0(sK2) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1864,c_1859]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3875,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,sK0) != iProver_top ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_3707,c_26,c_31,c_34,c_2225,c_2261,c_2538]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3884,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3015,c_3875]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_589,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.50/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 2.50/1.01      | ~ v1_funct_1(X2)
% 2.50/1.01      | ~ v1_funct_1(X4)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | ~ v1_relat_1(X4)
% 2.50/1.01      | X6 != X3
% 2.50/1.01      | X4 != X2
% 2.50/1.01      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.50/1.01      | k1_relat_1(X4) != X1 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_324]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_590,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X3)))
% 2.50/1.01      | ~ v1_funct_1(X1)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1))
% 2.50/1.01      | ~ v1_relat_1(X1)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_589]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_608,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.50/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.50/1.01      | ~ v1_funct_1(X1)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1))
% 2.50/1.01      | ~ v1_relat_1(X1)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1),X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.50/1.01      inference(forward_subsumption_resolution,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_590,c_341]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1373,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
% 2.50/1.01      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.50/1.01      | ~ v1_funct_1(X1_51)
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X1_51))
% 2.50/1.01      | ~ v1_relat_1(X1_51)
% 2.50/1.01      | k3_funct_2(k1_relat_1(X1_51),X1_52,X1_51,X0_51) = k1_funct_1(X1_51,X0_51) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_608]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1873,plain,
% 2.50/1.01      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
% 2.50/1.01      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.50/1.01      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 2.50/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3355,plain,
% 2.50/1.01      ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
% 2.50/1.01      | v1_funct_1(sK4) != iProver_top
% 2.50/1.01      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 2.50/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1864,c_1873]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3373,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,sK0) != iProver_top
% 2.50/1.01      | v1_funct_1(sK4) != iProver_top
% 2.50/1.01      | v1_xboole_0(sK0) = iProver_top
% 2.50/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_3355,c_2702]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3449,plain,
% 2.50/1.01      ( m1_subset_1(X0_51,sK0) != iProver_top
% 2.50/1.01      | k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_3373,c_26,c_31,c_2225,c_2261]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3450,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 2.50/1.01      | m1_subset_1(X0_51,sK0) != iProver_top ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_3449]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3458,plain,
% 2.50/1.01      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3015,c_3450]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3893,plain,
% 2.50/1.01      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_3884,c_3458]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_12,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/1.01      | ~ v1_partfun1(X3,X2)
% 2.50/1.01      | ~ m1_subset_1(X4,X1)
% 2.50/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | ~ v1_funct_1(X3)
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | v1_xboole_0(X2)
% 2.50/1.01      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_647,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X2,X3)
% 2.50/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 2.50/1.01      | ~ v1_funct_1(X4)
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v1_xboole_0(X3)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
% 2.50/1.01      | sK3 != X4
% 2.50/1.01      | sK0 != X1
% 2.50/1.01      | sK1 != X3 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_648,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0,sK0)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.50/1.01      | ~ m1_subset_1(X2,sK1)
% 2.50/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_funct_1(sK3)
% 2.50/1.01      | v1_xboole_0(sK0)
% 2.50/1.01      | v1_xboole_0(sK1)
% 2.50/1.01      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_647]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_652,plain,
% 2.50/1.01      ( ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_partfun1(X0,sK0)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.50/1.01      | ~ m1_subset_1(X2,sK1)
% 2.50/1.01      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_648,c_25,c_24,c_23,c_21]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_653,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0,sK0)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.50/1.01      | ~ m1_subset_1(X2,sK1)
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_652]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1371,plain,
% 2.50/1.01      ( ~ v1_partfun1(X0_51,sK0)
% 2.50/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
% 2.50/1.01      | ~ m1_subset_1(X1_51,sK1)
% 2.50/1.01      | ~ v1_funct_1(X0_51)
% 2.50/1.01      | k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51)) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_653]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1875,plain,
% 2.50/1.01      ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51))
% 2.50/1.01      | v1_partfun1(X0_51,sK0) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
% 2.50/1.01      | m1_subset_1(X1_51,sK1) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2863,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
% 2.50/1.01      | v1_partfun1(sK4,sK0) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_51,sK1) != iProver_top
% 2.50/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1864,c_1875]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2868,plain,
% 2.50/1.01      ( m1_subset_1(X0_51,sK1) != iProver_top
% 2.50/1.01      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51)) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_2863,c_31,c_34]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2869,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
% 2.50/1.01      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_2868]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2876,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_1863,c_2869]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2877,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_2876,c_2417]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_16,negated_conjecture,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1385,negated_conjecture,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2487,plain,
% 2.50/1.01      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_2417,c_1385]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3021,plain,
% 2.50/1.01      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_2877,c_2487]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(contradiction,plain,
% 2.50/1.01      ( $false ),
% 2.50/1.01      inference(minisat,[status(thm)],[c_3893,c_3021]) ).
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/1.01  
% 2.50/1.01  ------                               Statistics
% 2.50/1.01  
% 2.50/1.01  ------ General
% 2.50/1.01  
% 2.50/1.01  abstr_ref_over_cycles:                  0
% 2.50/1.01  abstr_ref_under_cycles:                 0
% 2.50/1.01  gc_basic_clause_elim:                   0
% 2.50/1.01  forced_gc_time:                         0
% 2.50/1.01  parsing_time:                           0.026
% 2.50/1.01  unif_index_cands_time:                  0.
% 2.50/1.01  unif_index_add_time:                    0.
% 2.50/1.01  orderings_time:                         0.
% 2.50/1.01  out_proof_time:                         0.009
% 2.50/1.01  total_time:                             0.161
% 2.50/1.01  num_of_symbols:                         56
% 2.50/1.01  num_of_terms:                           3793
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing
% 2.50/1.01  
% 2.50/1.01  num_of_splits:                          0
% 2.50/1.01  num_of_split_atoms:                     0
% 2.50/1.01  num_of_reused_defs:                     0
% 2.50/1.01  num_eq_ax_congr_red:                    11
% 2.50/1.01  num_of_sem_filtered_clauses:            1
% 2.50/1.01  num_of_subtypes:                        2
% 2.50/1.01  monotx_restored_types:                  0
% 2.50/1.01  sat_num_of_epr_types:                   0
% 2.50/1.01  sat_num_of_non_cyclic_types:            0
% 2.50/1.01  sat_guarded_non_collapsed_types:        1
% 2.50/1.01  num_pure_diseq_elim:                    0
% 2.50/1.01  simp_replaced_by:                       0
% 2.50/1.01  res_preprocessed:                       130
% 2.50/1.01  prep_upred:                             0
% 2.50/1.01  prep_unflattend:                        68
% 2.50/1.01  smt_new_axioms:                         0
% 2.50/1.01  pred_elim_cands:                        6
% 2.50/1.01  pred_elim:                              3
% 2.50/1.01  pred_elim_cl:                           1
% 2.50/1.01  pred_elim_cycles:                       8
% 2.50/1.01  merged_defs:                            0
% 2.50/1.01  merged_defs_ncl:                        0
% 2.50/1.01  bin_hyper_res:                          0
% 2.50/1.01  prep_cycles:                            4
% 2.50/1.01  pred_elim_time:                         0.024
% 2.50/1.01  splitting_time:                         0.
% 2.50/1.01  sem_filter_time:                        0.
% 2.50/1.01  monotx_time:                            0.
% 2.50/1.01  subtype_inf_time:                       0.
% 2.50/1.01  
% 2.50/1.01  ------ Problem properties
% 2.50/1.01  
% 2.50/1.01  clauses:                                24
% 2.50/1.01  conjectures:                            9
% 2.50/1.01  epr:                                    6
% 2.50/1.01  horn:                                   20
% 2.50/1.01  ground:                                 9
% 2.50/1.01  unary:                                  10
% 2.50/1.01  binary:                                 4
% 2.50/1.01  lits:                                   70
% 2.50/1.01  lits_eq:                                8
% 2.50/1.01  fd_pure:                                0
% 2.50/1.01  fd_pseudo:                              0
% 2.50/1.01  fd_cond:                                0
% 2.50/1.01  fd_pseudo_cond:                         1
% 2.50/1.01  ac_symbols:                             0
% 2.50/1.01  
% 2.50/1.01  ------ Propositional Solver
% 2.50/1.01  
% 2.50/1.01  prop_solver_calls:                      28
% 2.50/1.01  prop_fast_solver_calls:                 1217
% 2.50/1.01  smt_solver_calls:                       0
% 2.50/1.01  smt_fast_solver_calls:                  0
% 2.50/1.01  prop_num_of_clauses:                    1068
% 2.50/1.01  prop_preprocess_simplified:             4506
% 2.50/1.01  prop_fo_subsumed:                       65
% 2.50/1.01  prop_solver_time:                       0.
% 2.50/1.01  smt_solver_time:                        0.
% 2.50/1.01  smt_fast_solver_time:                   0.
% 2.50/1.01  prop_fast_solver_time:                  0.
% 2.50/1.01  prop_unsat_core_time:                   0.
% 2.50/1.01  
% 2.50/1.01  ------ QBF
% 2.50/1.01  
% 2.50/1.01  qbf_q_res:                              0
% 2.50/1.01  qbf_num_tautologies:                    0
% 2.50/1.01  qbf_prep_cycles:                        0
% 2.50/1.01  
% 2.50/1.01  ------ BMC1
% 2.50/1.01  
% 2.50/1.01  bmc1_current_bound:                     -1
% 2.50/1.01  bmc1_last_solved_bound:                 -1
% 2.50/1.01  bmc1_unsat_core_size:                   -1
% 2.50/1.01  bmc1_unsat_core_parents_size:           -1
% 2.50/1.01  bmc1_merge_next_fun:                    0
% 2.50/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.50/1.01  
% 2.50/1.01  ------ Instantiation
% 2.50/1.01  
% 2.50/1.01  inst_num_of_clauses:                    337
% 2.50/1.01  inst_num_in_passive:                    83
% 2.50/1.01  inst_num_in_active:                     243
% 2.50/1.01  inst_num_in_unprocessed:                11
% 2.50/1.01  inst_num_of_loops:                      260
% 2.50/1.01  inst_num_of_learning_restarts:          0
% 2.50/1.01  inst_num_moves_active_passive:          12
% 2.50/1.01  inst_lit_activity:                      0
% 2.50/1.01  inst_lit_activity_moves:                0
% 2.50/1.01  inst_num_tautologies:                   0
% 2.50/1.01  inst_num_prop_implied:                  0
% 2.50/1.01  inst_num_existing_simplified:           0
% 2.50/1.01  inst_num_eq_res_simplified:             0
% 2.50/1.01  inst_num_child_elim:                    0
% 2.50/1.01  inst_num_of_dismatching_blockings:      82
% 2.50/1.01  inst_num_of_non_proper_insts:           363
% 2.50/1.01  inst_num_of_duplicates:                 0
% 2.50/1.01  inst_inst_num_from_inst_to_res:         0
% 2.50/1.01  inst_dismatching_checking_time:         0.
% 2.50/1.01  
% 2.50/1.01  ------ Resolution
% 2.50/1.01  
% 2.50/1.01  res_num_of_clauses:                     0
% 2.50/1.01  res_num_in_passive:                     0
% 2.50/1.01  res_num_in_active:                      0
% 2.50/1.01  res_num_of_loops:                       134
% 2.50/1.01  res_forward_subset_subsumed:            63
% 2.50/1.01  res_backward_subset_subsumed:           2
% 2.50/1.01  res_forward_subsumed:                   0
% 2.50/1.01  res_backward_subsumed:                  0
% 2.50/1.01  res_forward_subsumption_resolution:     8
% 2.50/1.01  res_backward_subsumption_resolution:    0
% 2.50/1.01  res_clause_to_clause_subsumption:       144
% 2.50/1.01  res_orphan_elimination:                 0
% 2.50/1.01  res_tautology_del:                      63
% 2.50/1.01  res_num_eq_res_simplified:              0
% 2.50/1.01  res_num_sel_changes:                    0
% 2.50/1.01  res_moves_from_active_to_pass:          0
% 2.50/1.01  
% 2.50/1.01  ------ Superposition
% 2.50/1.01  
% 2.50/1.01  sup_time_total:                         0.
% 2.50/1.01  sup_time_generating:                    0.
% 2.50/1.01  sup_time_sim_full:                      0.
% 2.50/1.01  sup_time_sim_immed:                     0.
% 2.50/1.01  
% 2.50/1.01  sup_num_of_clauses:                     55
% 2.50/1.01  sup_num_in_active:                      49
% 2.50/1.01  sup_num_in_passive:                     6
% 2.50/1.01  sup_num_of_loops:                       50
% 2.50/1.01  sup_fw_superposition:                   33
% 2.50/1.01  sup_bw_superposition:                   9
% 2.50/1.01  sup_immediate_simplified:               13
% 2.50/1.01  sup_given_eliminated:                   0
% 2.50/1.01  comparisons_done:                       0
% 2.50/1.01  comparisons_avoided:                    0
% 2.50/1.01  
% 2.50/1.01  ------ Simplifications
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  sim_fw_subset_subsumed:                 3
% 2.50/1.01  sim_bw_subset_subsumed:                 0
% 2.50/1.01  sim_fw_subsumed:                        2
% 2.50/1.01  sim_bw_subsumed:                        0
% 2.50/1.01  sim_fw_subsumption_res:                 0
% 2.50/1.01  sim_bw_subsumption_res:                 0
% 2.50/1.01  sim_tautology_del:                      0
% 2.50/1.01  sim_eq_tautology_del:                   1
% 2.50/1.01  sim_eq_res_simp:                        0
% 2.50/1.01  sim_fw_demodulated:                     0
% 2.50/1.01  sim_bw_demodulated:                     2
% 2.50/1.01  sim_light_normalised:                   10
% 2.50/1.01  sim_joinable_taut:                      0
% 2.50/1.01  sim_joinable_simp:                      0
% 2.50/1.01  sim_ac_normalised:                      0
% 2.50/1.01  sim_smt_subsumption:                    0
% 2.50/1.01  
%------------------------------------------------------------------------------
