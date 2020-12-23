%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:20 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 869 expanded)
%              Number of clauses        :   94 ( 219 expanded)
%              Number of leaves         :   17 ( 314 expanded)
%              Depth                    :   21
%              Number of atoms          :  652 (6742 expanded)
%              Number of equality atoms :  160 ( 967 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f41,f40,f39,f38,f37])).

fof(f65,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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
                       => k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_730,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1108,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_343,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_11,c_4,c_2])).

cnf(c_348,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_722,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relat_1(X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_1116,plain,
    ( k1_relat_1(X0_50) = X0_51
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_2216,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_partfun1(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_1116])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_535,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_536,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1300,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51)))
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1302,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_2420,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_24,c_22,c_20,c_536,c_1302])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_254,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_250,c_2])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_254])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | m1_subset_1(k1_funct_1(X2,X5),X4)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | X5 != X0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_255])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_relat_1(X0))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_relat_1(X0_50))
    | m1_subset_1(k1_funct_1(X0_50,X1_50),X1_51)
    | ~ v1_funct_1(X0_50)
    | v1_xboole_0(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_279])).

cnf(c_1115,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_relat_1(X0_50)) != iProver_top
    | m1_subset_1(k1_funct_1(X0_50,X1_50),X1_51) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_xboole_0(k1_relat_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_1828,plain,
    ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_1115])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1910,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_27])).

cnf(c_1911,plain,
    ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1910])).

cnf(c_2425,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2420,c_1911])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2540,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_26])).

cnf(c_2541,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2540])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_729,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_5,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_422,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_7,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_440,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_422,c_7])).

cnf(c_719,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ m1_subset_1(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_xboole_0(X0_51)
    | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1119,plain,
    ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50)
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | m1_subset_1(X1_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_2044,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1119])).

cnf(c_25,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2065,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
    | m1_subset_1(X0_50,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_25,c_30,c_33])).

cnf(c_2548,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_2065])).

cnf(c_2650,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1108,c_2548])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_448,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X0,X2) = k1_funct_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_718,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ m1_subset_1(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_xboole_0(X0_51)
    | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_1120,plain,
    ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50)
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | m1_subset_1(X1_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1542,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1120])).

cnf(c_1813,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | m1_subset_1(X0_50,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_25,c_30,c_33])).

cnf(c_2549,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_1813])).

cnf(c_2614,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1108,c_2549])).

cnf(c_2651,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2650,c_2614])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_472,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_473,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_24,c_23,c_22,c_20])).

cnf(c_478,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_717,plain,
    ( ~ v1_partfun1(X0_50,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ m1_subset_1(X1_50,sK1)
    | ~ v1_funct_1(X0_50)
    | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50)) ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_1121,plain,
    ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50))
    | v1_partfun1(X0_50,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_1760,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1121])).

cnf(c_1765,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1760,c_30,c_33])).

cnf(c_1766,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1765])).

cnf(c_1773,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1108,c_1766])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_23,c_22,c_20])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_522])).

cnf(c_1123,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_1642,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1108,c_1123])).

cnf(c_1774,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1773,c_1642])).

cnf(c_15,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_732,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1644,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1642,c_732])).

cnf(c_2130,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1774,c_1644])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2651,c_2130])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.56/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.00  
% 2.56/1.00  ------  iProver source info
% 2.56/1.00  
% 2.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.00  git: non_committed_changes: false
% 2.56/1.00  git: last_make_outside_of_git: false
% 2.56/1.00  
% 2.56/1.00  ------ 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options
% 2.56/1.00  
% 2.56/1.00  --out_options                           all
% 2.56/1.00  --tptp_safe_out                         true
% 2.56/1.00  --problem_path                          ""
% 2.56/1.00  --include_path                          ""
% 2.56/1.00  --clausifier                            res/vclausify_rel
% 2.56/1.00  --clausifier_options                    --mode clausify
% 2.56/1.00  --stdin                                 false
% 2.56/1.00  --stats_out                             all
% 2.56/1.00  
% 2.56/1.00  ------ General Options
% 2.56/1.00  
% 2.56/1.00  --fof                                   false
% 2.56/1.00  --time_out_real                         305.
% 2.56/1.00  --time_out_virtual                      -1.
% 2.56/1.00  --symbol_type_check                     false
% 2.56/1.00  --clausify_out                          false
% 2.56/1.00  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     num_symb
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       true
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  ------ Parsing...
% 2.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.00  ------ Proving...
% 2.56/1.00  ------ Problem Properties 
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  clauses                                 20
% 2.56/1.00  conjectures                             9
% 2.56/1.00  EPR                                     7
% 2.56/1.00  Horn                                    16
% 2.56/1.00  unary                                   10
% 2.56/1.00  binary                                  3
% 2.56/1.00  lits                                    54
% 2.56/1.00  lits eq                                 8
% 2.56/1.00  fd_pure                                 0
% 2.56/1.00  fd_pseudo                               0
% 2.56/1.00  fd_cond                                 0
% 2.56/1.00  fd_pseudo_cond                          1
% 2.56/1.00  AC symbols                              0
% 2.56/1.00  
% 2.56/1.00  ------ Schedule dynamic 5 is on 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ 
% 2.56/1.00  Current options:
% 2.56/1.00  ------ 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options
% 2.56/1.00  
% 2.56/1.00  --out_options                           all
% 2.56/1.00  --tptp_safe_out                         true
% 2.56/1.00  --problem_path                          ""
% 2.56/1.00  --include_path                          ""
% 2.56/1.00  --clausifier                            res/vclausify_rel
% 2.56/1.00  --clausifier_options                    --mode clausify
% 2.56/1.00  --stdin                                 false
% 2.56/1.00  --stats_out                             all
% 2.56/1.00  
% 2.56/1.00  ------ General Options
% 2.56/1.00  
% 2.56/1.00  --fof                                   false
% 2.56/1.00  --time_out_real                         305.
% 2.56/1.00  --time_out_virtual                      -1.
% 2.56/1.00  --symbol_type_check                     false
% 2.56/1.00  --clausify_out                          false
% 2.56/1.00  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     none
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       false
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ Proving...
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  % SZS status Theorem for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  fof(f12,conjecture,(
% 2.56/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f13,negated_conjecture,(
% 2.56/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.56/1.00    inference(negated_conjecture,[],[f12])).
% 2.56/1.00  
% 2.56/1.00  fof(f34,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f13])).
% 2.56/1.00  
% 2.56/1.00  fof(f35,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.56/1.00    inference(flattening,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f41,plain,(
% 2.56/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f40,plain,(
% 2.56/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f39,plain,(
% 2.56/1.00    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f38,plain,(
% 2.56/1.00    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f37,plain,(
% 2.56/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f42,plain,(
% 2.56/1.00    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f41,f40,f39,f38,f37])).
% 2.56/1.00  
% 2.56/1.00  fof(f65,plain,(
% 2.56/1.00    m1_subset_1(sK5,sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f62,plain,(
% 2.56/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f4,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f19,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f4])).
% 2.56/1.00  
% 2.56/1.00  fof(f46,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f19])).
% 2.56/1.00  
% 2.56/1.00  fof(f8,axiom,(
% 2.56/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f26,plain,(
% 2.56/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.56/1.00    inference(ennf_transformation,[],[f8])).
% 2.56/1.00  
% 2.56/1.00  fof(f27,plain,(
% 2.56/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/1.00    inference(flattening,[],[f26])).
% 2.56/1.00  
% 2.56/1.00  fof(f36,plain,(
% 2.56/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/1.00    inference(nnf_transformation,[],[f27])).
% 2.56/1.00  
% 2.56/1.00  fof(f53,plain,(
% 2.56/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f36])).
% 2.56/1.00  
% 2.56/1.00  fof(f3,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f18,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f3])).
% 2.56/1.00  
% 2.56/1.00  fof(f45,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f18])).
% 2.56/1.00  
% 2.56/1.00  fof(f58,plain,(
% 2.56/1.00    ~v1_xboole_0(sK0)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f60,plain,(
% 2.56/1.00    v1_funct_1(sK3)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f7,axiom,(
% 2.56/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f24,plain,(
% 2.56/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/1.00    inference(ennf_transformation,[],[f7])).
% 2.56/1.00  
% 2.56/1.00  fof(f25,plain,(
% 2.56/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/1.00    inference(flattening,[],[f24])).
% 2.56/1.00  
% 2.56/1.00  fof(f52,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f25])).
% 2.56/1.00  
% 2.56/1.00  fof(f61,plain,(
% 2.56/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f1,axiom,(
% 2.56/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f14,plain,(
% 2.56/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.56/1.00    inference(ennf_transformation,[],[f1])).
% 2.56/1.00  
% 2.56/1.00  fof(f15,plain,(
% 2.56/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.56/1.00    inference(flattening,[],[f14])).
% 2.56/1.00  
% 2.56/1.00  fof(f43,plain,(
% 2.56/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f15])).
% 2.56/1.00  
% 2.56/1.00  fof(f47,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f19])).
% 2.56/1.00  
% 2.56/1.00  fof(f2,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f16,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.56/1.00    inference(ennf_transformation,[],[f2])).
% 2.56/1.00  
% 2.56/1.00  fof(f17,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.56/1.00    inference(flattening,[],[f16])).
% 2.56/1.00  
% 2.56/1.00  fof(f44,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f17])).
% 2.56/1.00  
% 2.56/1.00  fof(f59,plain,(
% 2.56/1.00    ~v1_xboole_0(sK1)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f64,plain,(
% 2.56/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f5,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f20,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f5])).
% 2.56/1.00  
% 2.56/1.00  fof(f21,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(flattening,[],[f20])).
% 2.56/1.00  
% 2.56/1.00  fof(f49,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f21])).
% 2.56/1.00  
% 2.56/1.00  fof(f10,axiom,(
% 2.56/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f30,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f10])).
% 2.56/1.00  
% 2.56/1.00  fof(f31,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.56/1.00    inference(flattening,[],[f30])).
% 2.56/1.00  
% 2.56/1.00  fof(f56,plain,(
% 2.56/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f31])).
% 2.56/1.00  
% 2.56/1.00  fof(f6,axiom,(
% 2.56/1.00    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f22,plain,(
% 2.56/1.00    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.56/1.00    inference(ennf_transformation,[],[f6])).
% 2.56/1.00  
% 2.56/1.00  fof(f23,plain,(
% 2.56/1.00    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.56/1.00    inference(flattening,[],[f22])).
% 2.56/1.00  
% 2.56/1.00  fof(f50,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f23])).
% 2.56/1.00  
% 2.56/1.00  fof(f63,plain,(
% 2.56/1.00    v1_funct_1(sK4)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f66,plain,(
% 2.56/1.00    v1_partfun1(sK4,sK0)),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  fof(f9,axiom,(
% 2.56/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f28,plain,(
% 2.56/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.56/1.00    inference(ennf_transformation,[],[f9])).
% 2.56/1.00  
% 2.56/1.00  fof(f29,plain,(
% 2.56/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.56/1.00    inference(flattening,[],[f28])).
% 2.56/1.00  
% 2.56/1.00  fof(f55,plain,(
% 2.56/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f29])).
% 2.56/1.00  
% 2.56/1.00  fof(f11,axiom,(
% 2.56/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)))))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f32,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f11])).
% 2.56/1.00  
% 2.56/1.00  fof(f33,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.56/1.00    inference(flattening,[],[f32])).
% 2.56/1.00  
% 2.56/1.00  fof(f57,plain,(
% 2.56/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f33])).
% 2.56/1.00  
% 2.56/1.00  fof(f67,plain,(
% 2.56/1.00    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.56/1.00    inference(cnf_transformation,[],[f42])).
% 2.56/1.00  
% 2.56/1.00  cnf(c_17,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK5,sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_730,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK5,sK1) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1108,plain,
% 2.56/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_20,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_727,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1111,plain,
% 2.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_4,plain,
% 2.56/1.00      ( v4_relat_1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_11,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ v4_relat_1(X0,X1)
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | k1_relat_1(X0) = X1 ),
% 2.56/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_343,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | k1_relat_1(X0) = X1 ),
% 2.56/1.00      inference(resolution,[status(thm)],[c_4,c_11]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | v1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_347,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_partfun1(X0,X1)
% 2.56/1.00      | k1_relat_1(X0) = X1 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_343,c_11,c_4,c_2]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_348,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relat_1(X0) = X1 ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_347]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_722,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0_50,X0_51)
% 2.56/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.56/1.00      | k1_relat_1(X0_50) = X0_51 ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_348]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1116,plain,
% 2.56/1.00      ( k1_relat_1(X0_50) = X0_51
% 2.56/1.00      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2216,plain,
% 2.56/1.00      ( k1_relat_1(sK3) = sK1 | v1_partfun1(sK3,sK1) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1111,c_1116]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_24,negated_conjecture,
% 2.56/1.00      ( ~ v1_xboole_0(sK0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_22,negated_conjecture,
% 2.56/1.00      ( v1_funct_1(sK3) ),
% 2.56/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_8,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X2) ),
% 2.56/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_21,negated_conjecture,
% 2.56/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_535,plain,
% 2.56/1.00      ( v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X2)
% 2.56/1.00      | sK3 != X0
% 2.56/1.00      | sK0 != X2
% 2.56/1.00      | sK1 != X1 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_536,plain,
% 2.56/1.00      ( v1_partfun1(sK3,sK1)
% 2.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.56/1.00      | ~ v1_funct_1(sK3)
% 2.56/1.00      | v1_xboole_0(sK0) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1300,plain,
% 2.56/1.00      ( ~ v1_partfun1(sK3,sK1)
% 2.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51)))
% 2.56/1.00      | k1_relat_1(sK3) = sK1 ),
% 2.56/1.00      inference(instantiation,[status(thm)],[c_722]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1302,plain,
% 2.56/1.00      ( ~ v1_partfun1(sK3,sK1)
% 2.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.56/1.00      | k1_relat_1(sK3) = sK1 ),
% 2.56/1.00      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2420,plain,
% 2.56/1.00      ( k1_relat_1(sK3) = sK1 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_2216,c_24,c_22,c_20,c_536,c_1302]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_0,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3,plain,
% 2.56/1.00      ( v5_relat_1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1,plain,
% 2.56/1.00      ( ~ v5_relat_1(X0,X1)
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.56/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_250,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.56/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_254,plain,
% 2.56/1.00      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_250,c_2]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_255,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.56/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_254]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_278,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X2,X5),X4)
% 2.56/1.00      | ~ v1_funct_1(X2)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | X5 != X0
% 2.56/1.00      | k1_relat_1(X2) != X1 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_255]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_279,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ m1_subset_1(X3,k1_relat_1(X0))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(k1_relat_1(X0)) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_278]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_723,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.56/1.00      | ~ m1_subset_1(X1_50,k1_relat_1(X0_50))
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0_50,X1_50),X1_51)
% 2.56/1.00      | ~ v1_funct_1(X0_50)
% 2.56/1.00      | v1_xboole_0(k1_relat_1(X0_50)) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_279]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1115,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.56/1.00      | m1_subset_1(X1_50,k1_relat_1(X0_50)) != iProver_top
% 2.56/1.00      | m1_subset_1(k1_funct_1(X0_50,X1_50),X1_51) = iProver_top
% 2.56/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.56/1.00      | v1_xboole_0(k1_relat_1(X0_50)) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1828,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.56/1.00      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.56/1.00      | v1_funct_1(sK3) != iProver_top
% 2.56/1.00      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1111,c_1115]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_27,plain,
% 2.56/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1910,plain,
% 2.56/1.00      ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.56/1.00      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_1828,c_27]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1911,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.56/1.00      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.56/1.00      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_1910]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2425,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.56/1.00      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.56/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_2420,c_1911]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_23,negated_conjecture,
% 2.56/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_26,plain,
% 2.56/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2540,plain,
% 2.56/1.00      ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_2425,c_26]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2541,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.56/1.00      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_2540]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_18,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_729,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1109,plain,
% 2.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5,plain,
% 2.56/1.00      ( v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_13,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X3,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X2)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 2.56/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_422,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | v1_xboole_0(X3)
% 2.56/1.00      | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
% 2.56/1.00      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_7,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_xboole_0(X2)
% 2.56/1.00      | v1_xboole_0(X1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_440,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
% 2.56/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_422,c_7]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_719,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0_50,X0_51)
% 2.56/1.00      | ~ m1_subset_1(X1_50,X0_51)
% 2.56/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.56/1.00      | ~ v1_funct_1(X0_50)
% 2.56/1.00      | v1_xboole_0(X0_51)
% 2.56/1.00      | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_440]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1119,plain,
% 2.56/1.00      ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50)
% 2.56/1.00      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.56/1.00      | m1_subset_1(X1_50,X0_51) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.56/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.56/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2044,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
% 2.56/1.00      | v1_partfun1(sK4,sK0) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,sK0) != iProver_top
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top
% 2.56/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1109,c_1119]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_25,plain,
% 2.56/1.00      ( v1_xboole_0(sK0) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_19,negated_conjecture,
% 2.56/1.00      ( v1_funct_1(sK4) ),
% 2.56/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_30,plain,
% 2.56/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_16,negated_conjecture,
% 2.56/1.00      ( v1_partfun1(sK4,sK0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_33,plain,
% 2.56/1.00      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2065,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
% 2.56/1.00      | m1_subset_1(X0_50,sK0) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_2044,c_25,c_30,c_33]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2548,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0_50))
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2541,c_2065]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2650,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1108,c_2548]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_12,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X3,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.56/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_448,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,X1)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X1,X3,X0,X2) = k1_funct_1(X0,X2) ),
% 2.56/1.00      inference(resolution,[status(thm)],[c_5,c_12]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_718,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0_50,X0_51)
% 2.56/1.00      | ~ m1_subset_1(X1_50,X0_51)
% 2.56/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.56/1.00      | ~ v1_funct_1(X0_50)
% 2.56/1.00      | v1_xboole_0(X0_51)
% 2.56/1.00      | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_448]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1120,plain,
% 2.56/1.00      ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50)
% 2.56/1.00      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.56/1.00      | m1_subset_1(X1_50,X0_51) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.56/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.56/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1542,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.56/1.00      | v1_partfun1(sK4,sK0) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,sK0) != iProver_top
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top
% 2.56/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1109,c_1120]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1813,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.56/1.00      | m1_subset_1(X0_50,sK0) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_1542,c_25,c_30,c_33]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2549,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2541,c_1813]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2614,plain,
% 2.56/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1108,c_2549]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2651,plain,
% 2.56/1.00      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_2650,c_2614]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_14,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ v1_partfun1(X3,X2)
% 2.56/1.00      | ~ m1_subset_1(X4,X1)
% 2.56/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | ~ v1_funct_1(X3)
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | v1_xboole_0(X2)
% 2.56/1.00      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_472,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,X3)
% 2.56/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 2.56/1.00      | ~ v1_funct_1(X4)
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | v1_xboole_0(X3)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
% 2.56/1.00      | sK3 != X4
% 2.56/1.00      | sK0 != X1
% 2.56/1.00      | sK1 != X3 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_473,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,sK0)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.56/1.00      | ~ m1_subset_1(X2,sK1)
% 2.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v1_funct_1(sK3)
% 2.56/1.00      | v1_xboole_0(sK0)
% 2.56/1.00      | v1_xboole_0(sK1)
% 2.56/1.00      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_477,plain,
% 2.56/1.00      ( ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v1_partfun1(X0,sK0)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.56/1.00      | ~ m1_subset_1(X2,sK1)
% 2.56/1.00      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_473,c_24,c_23,c_22,c_20]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_478,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0,sK0)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.56/1.00      | ~ m1_subset_1(X2,sK1)
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_477]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_717,plain,
% 2.56/1.00      ( ~ v1_partfun1(X0_50,sK0)
% 2.56/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 2.56/1.00      | ~ m1_subset_1(X1_50,sK1)
% 2.56/1.00      | ~ v1_funct_1(X0_50)
% 2.56/1.00      | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50)) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_478]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1121,plain,
% 2.56/1.00      ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50))
% 2.56/1.00      | v1_partfun1(X0_50,sK0) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 2.56/1.00      | m1_subset_1(X1_50,sK1) != iProver_top
% 2.56/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1760,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.56/1.00      | v1_partfun1(sK4,sK0) != iProver_top
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1109,c_1121]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1765,plain,
% 2.56/1.00      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.56/1.00      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_1760,c_30,c_33]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1766,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_1765]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1773,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1108,c_1766]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_517,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,X1)
% 2.56/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.56/1.00      | ~ v1_funct_1(X2)
% 2.56/1.00      | v1_xboole_0(X1)
% 2.56/1.00      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.56/1.00      | sK3 != X2
% 2.56/1.00      | sK0 != X3
% 2.56/1.00      | sK1 != X1 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_518,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,sK1)
% 2.56/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.56/1.00      | ~ v1_funct_1(sK3)
% 2.56/1.00      | v1_xboole_0(sK1)
% 2.56/1.00      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_522,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,sK1)
% 2.56/1.00      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_518,c_23,c_22,c_20]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_715,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0_50,sK1)
% 2.56/1.00      | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_522]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1123,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
% 2.56/1.00      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1642,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_1108,c_1123]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1774,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(light_normalisation,[status(thm)],[c_1773,c_1642]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_15,negated_conjecture,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_732,negated_conjecture,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.56/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_1644,plain,
% 2.56/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1642,c_732]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2130,plain,
% 2.56/1.00      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.56/1.00      inference(demodulation,[status(thm)],[c_1774,c_1644]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(contradiction,plain,
% 2.56/1.00      ( $false ),
% 2.56/1.00      inference(minisat,[status(thm)],[c_2651,c_2130]) ).
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  ------                               Statistics
% 2.56/1.00  
% 2.56/1.00  ------ General
% 2.56/1.00  
% 2.56/1.00  abstr_ref_over_cycles:                  0
% 2.56/1.00  abstr_ref_under_cycles:                 0
% 2.56/1.00  gc_basic_clause_elim:                   0
% 2.56/1.00  forced_gc_time:                         0
% 2.56/1.00  parsing_time:                           0.039
% 2.56/1.00  unif_index_cands_time:                  0.
% 2.56/1.00  unif_index_add_time:                    0.
% 2.56/1.00  orderings_time:                         0.
% 2.56/1.00  out_proof_time:                         0.042
% 2.56/1.00  total_time:                             0.315
% 2.56/1.00  num_of_symbols:                         56
% 2.56/1.00  num_of_terms:                           2817
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing
% 2.56/1.00  
% 2.56/1.00  num_of_splits:                          0
% 2.56/1.00  num_of_split_atoms:                     0
% 2.56/1.00  num_of_reused_defs:                     0
% 2.56/1.00  num_eq_ax_congr_red:                    9
% 2.56/1.00  num_of_sem_filtered_clauses:            1
% 2.56/1.00  num_of_subtypes:                        3
% 2.56/1.00  monotx_restored_types:                  0
% 2.56/1.00  sat_num_of_epr_types:                   0
% 2.56/1.00  sat_num_of_non_cyclic_types:            0
% 2.56/1.00  sat_guarded_non_collapsed_types:        1
% 2.56/1.00  num_pure_diseq_elim:                    0
% 2.56/1.00  simp_replaced_by:                       0
% 2.56/1.00  res_preprocessed:                       114
% 2.56/1.00  prep_upred:                             0
% 2.56/1.00  prep_unflattend:                        16
% 2.56/1.00  smt_new_axioms:                         0
% 2.56/1.00  pred_elim_cands:                        4
% 2.56/1.00  pred_elim:                              5
% 2.56/1.00  pred_elim_cl:                           3
% 2.56/1.00  pred_elim_cycles:                       8
% 2.56/1.00  merged_defs:                            0
% 2.56/1.00  merged_defs_ncl:                        0
% 2.56/1.00  bin_hyper_res:                          0
% 2.56/1.00  prep_cycles:                            4
% 2.56/1.00  pred_elim_time:                         0.008
% 2.56/1.00  splitting_time:                         0.
% 2.56/1.00  sem_filter_time:                        0.
% 2.56/1.00  monotx_time:                            0.
% 2.56/1.00  subtype_inf_time:                       0.
% 2.56/1.00  
% 2.56/1.00  ------ Problem properties
% 2.56/1.00  
% 2.56/1.00  clauses:                                20
% 2.56/1.00  conjectures:                            9
% 2.56/1.00  epr:                                    7
% 2.56/1.00  horn:                                   16
% 2.56/1.00  ground:                                 10
% 2.56/1.00  unary:                                  10
% 2.56/1.00  binary:                                 3
% 2.56/1.00  lits:                                   54
% 2.56/1.00  lits_eq:                                8
% 2.56/1.00  fd_pure:                                0
% 2.56/1.00  fd_pseudo:                              0
% 2.56/1.00  fd_cond:                                0
% 2.56/1.00  fd_pseudo_cond:                         1
% 2.56/1.00  ac_symbols:                             0
% 2.56/1.00  
% 2.56/1.00  ------ Propositional Solver
% 2.56/1.00  
% 2.56/1.00  prop_solver_calls:                      27
% 2.56/1.00  prop_fast_solver_calls:                 876
% 2.56/1.00  smt_solver_calls:                       0
% 2.56/1.00  smt_fast_solver_calls:                  0
% 2.56/1.00  prop_num_of_clauses:                    857
% 2.56/1.00  prop_preprocess_simplified:             3553
% 2.56/1.00  prop_fo_subsumed:                       38
% 2.56/1.00  prop_solver_time:                       0.
% 2.56/1.00  smt_solver_time:                        0.
% 2.56/1.00  smt_fast_solver_time:                   0.
% 2.56/1.00  prop_fast_solver_time:                  0.
% 2.56/1.00  prop_unsat_core_time:                   0.
% 2.56/1.00  
% 2.56/1.00  ------ QBF
% 2.56/1.00  
% 2.56/1.00  qbf_q_res:                              0
% 2.56/1.00  qbf_num_tautologies:                    0
% 2.56/1.00  qbf_prep_cycles:                        0
% 2.56/1.00  
% 2.56/1.00  ------ BMC1
% 2.56/1.00  
% 2.56/1.00  bmc1_current_bound:                     -1
% 2.56/1.00  bmc1_last_solved_bound:                 -1
% 2.56/1.00  bmc1_unsat_core_size:                   -1
% 2.56/1.00  bmc1_unsat_core_parents_size:           -1
% 2.56/1.00  bmc1_merge_next_fun:                    0
% 2.56/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation
% 2.56/1.00  
% 2.56/1.00  inst_num_of_clauses:                    266
% 2.56/1.00  inst_num_in_passive:                    60
% 2.56/1.00  inst_num_in_active:                     205
% 2.56/1.00  inst_num_in_unprocessed:                1
% 2.56/1.00  inst_num_of_loops:                      210
% 2.56/1.00  inst_num_of_learning_restarts:          0
% 2.56/1.00  inst_num_moves_active_passive:          0
% 2.56/1.00  inst_lit_activity:                      0
% 2.56/1.00  inst_lit_activity_moves:                0
% 2.56/1.00  inst_num_tautologies:                   0
% 2.56/1.00  inst_num_prop_implied:                  0
% 2.56/1.00  inst_num_existing_simplified:           0
% 2.56/1.00  inst_num_eq_res_simplified:             0
% 2.56/1.00  inst_num_child_elim:                    0
% 2.56/1.00  inst_num_of_dismatching_blockings:      19
% 2.56/1.00  inst_num_of_non_proper_insts:           265
% 2.56/1.00  inst_num_of_duplicates:                 0
% 2.56/1.00  inst_inst_num_from_inst_to_res:         0
% 2.56/1.00  inst_dismatching_checking_time:         0.
% 2.56/1.00  
% 2.56/1.00  ------ Resolution
% 2.56/1.00  
% 2.56/1.00  res_num_of_clauses:                     0
% 2.56/1.00  res_num_in_passive:                     0
% 2.56/1.00  res_num_in_active:                      0
% 2.56/1.00  res_num_of_loops:                       118
% 2.56/1.00  res_forward_subset_subsumed:            45
% 2.56/1.00  res_backward_subset_subsumed:           0
% 2.56/1.00  res_forward_subsumed:                   0
% 2.56/1.00  res_backward_subsumed:                  0
% 2.56/1.00  res_forward_subsumption_resolution:     3
% 2.56/1.00  res_backward_subsumption_resolution:    0
% 2.56/1.00  res_clause_to_clause_subsumption:       63
% 2.56/1.00  res_orphan_elimination:                 0
% 2.56/1.00  res_tautology_del:                      29
% 2.56/1.00  res_num_eq_res_simplified:              0
% 2.56/1.00  res_num_sel_changes:                    0
% 2.56/1.00  res_moves_from_active_to_pass:          0
% 2.56/1.00  
% 2.56/1.00  ------ Superposition
% 2.56/1.00  
% 2.56/1.00  sup_time_total:                         0.
% 2.56/1.00  sup_time_generating:                    0.
% 2.56/1.00  sup_time_sim_full:                      0.
% 2.56/1.00  sup_time_sim_immed:                     0.
% 2.56/1.00  
% 2.56/1.00  sup_num_of_clauses:                     36
% 2.56/1.00  sup_num_in_active:                      35
% 2.56/1.00  sup_num_in_passive:                     1
% 2.56/1.00  sup_num_of_loops:                       40
% 2.56/1.00  sup_fw_superposition:                   18
% 2.56/1.00  sup_bw_superposition:                   6
% 2.56/1.00  sup_immediate_simplified:               8
% 2.56/1.00  sup_given_eliminated:                   0
% 2.56/1.00  comparisons_done:                       0
% 2.56/1.00  comparisons_avoided:                    0
% 2.56/1.00  
% 2.56/1.00  ------ Simplifications
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  sim_fw_subset_subsumed:                 1
% 2.56/1.00  sim_bw_subset_subsumed:                 2
% 2.56/1.00  sim_fw_subsumed:                        4
% 2.56/1.00  sim_bw_subsumed:                        0
% 2.56/1.00  sim_fw_subsumption_res:                 0
% 2.56/1.00  sim_bw_subsumption_res:                 0
% 2.56/1.00  sim_tautology_del:                      0
% 2.56/1.00  sim_eq_tautology_del:                   0
% 2.56/1.00  sim_eq_res_simp:                        0
% 2.56/1.00  sim_fw_demodulated:                     0
% 2.56/1.00  sim_bw_demodulated:                     6
% 2.56/1.00  sim_light_normalised:                   5
% 2.56/1.00  sim_joinable_taut:                      0
% 2.56/1.00  sim_joinable_simp:                      0
% 2.56/1.00  sim_ac_normalised:                      0
% 2.56/1.00  sim_smt_subsumption:                    0
% 2.56/1.00  
%------------------------------------------------------------------------------
