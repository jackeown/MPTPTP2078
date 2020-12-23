%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:09 EST 2020

% Result     : CounterSatisfiable 1.58s
% Output     : Saturation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  188 (1417 expanded)
%              Number of clauses        :  112 ( 313 expanded)
%              Number of leaves         :   29 ( 454 expanded)
%              Depth                    :   21
%              Number of atoms          :  949 (8517 expanded)
%              Number of equality atoms :  202 ( 359 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK3)
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f47,f46,f45])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k3_struct_0(X0),X0,X0)
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_311,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_308,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_307,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_304,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_301,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_300,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_296,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_295,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_294,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_292,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_289,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_22])).

cnf(c_173,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_358,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
    | sK3 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_173,c_23])).

cnf(c_359,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_363,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_26,c_24])).

cnf(c_364,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_824,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
    | sK1 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_364])).

cnf(c_825,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_366,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_190,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_22,c_18,c_17,c_9])).

cnf(c_191,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_669,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_25])).

cnf(c_670,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_827,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_29,c_28,c_27,c_25,c_366,c_670])).

cnf(c_1079,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_827])).

cnf(c_677,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_678,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_680,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_27])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_29,c_27])).

cnf(c_1013,plain,
    ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_680,c_905])).

cnf(c_1014,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_1074,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1014])).

cnf(c_672,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_29,c_28,c_27])).

cnf(c_1080,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_672])).

cnf(c_1122,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_1079,c_1074,c_1080])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_340,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_3,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_397,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v2_pre_topc(X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_398,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_16,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_402,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_16,c_15,c_13,c_340])).

cnf(c_403,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
    | ~ l1_pre_topc(X1)
    | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_408,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
    | ~ l1_pre_topc(X1)
    | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_14,c_12])).

cnf(c_409,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
    | ~ l1_pre_topc(X1)
    | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_408])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_409,c_25])).

cnf(c_653,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_655,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_29,c_28,c_27,c_26])).

cnf(c_656,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_868,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_340,c_656])).

cnf(c_732,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_733,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_735,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_29,c_28,c_27])).

cnf(c_959,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k8_tmap_1(sK1,sK2) != X0
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_868,c_735])).

cnf(c_960,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_688,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k8_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_689,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_962,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_29,c_28,c_27,c_689])).

cnf(c_976,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k3_struct_0(sK1) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_24,c_962])).

cnf(c_1078,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k3_struct_0(sK1) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_986,plain,
    ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_905])).

cnf(c_987,plain,
    ( k7_tmap_1(sK1,sK3) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_1077,plain,
    ( k7_tmap_1(sK1,sK3) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_721,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_722,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_724,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_29,c_28,c_27])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_724])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_29,c_28,c_27,c_689,c_733])).

cnf(c_994,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_923])).

cnf(c_995,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),sK3) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_1076,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),sK3) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_995])).

cnf(c_1002,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k3_struct_0(sK1) != u1_struct_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_962,c_680])).

cnf(c_1075,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k3_struct_0(sK1) != u1_struct_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1002])).

cnf(c_1018,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_680,c_923])).

cnf(c_1019,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1018])).

cnf(c_1073,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1019])).

cnf(c_699,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_700,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_702,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_29,c_28,c_27])).

cnf(c_1026,plain,
    ( k9_tmap_1(sK1,sK2) != X0
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_702,c_905])).

cnf(c_1027,plain,
    ( k7_tmap_1(sK1,k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_1072,plain,
    ( k7_tmap_1(sK1,k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1027])).

cnf(c_1034,plain,
    ( k9_tmap_1(sK1,sK2) != X0
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(resolution_lifted,[status(thm)],[c_702,c_923])).

cnf(c_1035,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_1071,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_1035])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:06:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.58/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/0.99  
% 1.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/0.99  
% 1.58/0.99  ------  iProver source info
% 1.58/0.99  
% 1.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/0.99  git: non_committed_changes: false
% 1.58/0.99  git: last_make_outside_of_git: false
% 1.58/0.99  
% 1.58/0.99  ------ 
% 1.58/0.99  
% 1.58/0.99  ------ Input Options
% 1.58/0.99  
% 1.58/0.99  --out_options                           all
% 1.58/0.99  --tptp_safe_out                         true
% 1.58/0.99  --problem_path                          ""
% 1.58/0.99  --include_path                          ""
% 1.58/0.99  --clausifier                            res/vclausify_rel
% 1.58/0.99  --clausifier_options                    --mode clausify
% 1.58/0.99  --stdin                                 false
% 1.58/0.99  --stats_out                             all
% 1.58/0.99  
% 1.58/0.99  ------ General Options
% 1.58/0.99  
% 1.58/0.99  --fof                                   false
% 1.58/0.99  --time_out_real                         305.
% 1.58/0.99  --time_out_virtual                      -1.
% 1.58/0.99  --symbol_type_check                     false
% 1.58/0.99  --clausify_out                          false
% 1.58/0.99  --sig_cnt_out                           false
% 1.58/0.99  --trig_cnt_out                          false
% 1.58/0.99  --trig_cnt_out_tolerance                1.
% 1.58/0.99  --trig_cnt_out_sk_spl                   false
% 1.58/0.99  --abstr_cl_out                          false
% 1.58/0.99  
% 1.58/0.99  ------ Global Options
% 1.58/0.99  
% 1.58/0.99  --schedule                              default
% 1.58/0.99  --add_important_lit                     false
% 1.58/0.99  --prop_solver_per_cl                    1000
% 1.58/0.99  --min_unsat_core                        false
% 1.58/0.99  --soft_assumptions                      false
% 1.58/0.99  --soft_lemma_size                       3
% 1.58/0.99  --prop_impl_unit_size                   0
% 1.58/0.99  --prop_impl_unit                        []
% 1.58/0.99  --share_sel_clauses                     true
% 1.58/0.99  --reset_solvers                         false
% 1.58/0.99  --bc_imp_inh                            [conj_cone]
% 1.58/0.99  --conj_cone_tolerance                   3.
% 1.58/0.99  --extra_neg_conj                        none
% 1.58/0.99  --large_theory_mode                     true
% 1.58/0.99  --prolific_symb_bound                   200
% 1.58/0.99  --lt_threshold                          2000
% 1.58/0.99  --clause_weak_htbl                      true
% 1.58/0.99  --gc_record_bc_elim                     false
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing Options
% 1.58/0.99  
% 1.58/0.99  --preprocessing_flag                    true
% 1.58/0.99  --time_out_prep_mult                    0.1
% 1.58/0.99  --splitting_mode                        input
% 1.58/0.99  --splitting_grd                         true
% 1.58/0.99  --splitting_cvd                         false
% 1.58/0.99  --splitting_cvd_svl                     false
% 1.58/0.99  --splitting_nvd                         32
% 1.58/0.99  --sub_typing                            true
% 1.58/0.99  --prep_gs_sim                           true
% 1.58/0.99  --prep_unflatten                        true
% 1.58/0.99  --prep_res_sim                          true
% 1.58/0.99  --prep_upred                            true
% 1.58/0.99  --prep_sem_filter                       exhaustive
% 1.58/0.99  --prep_sem_filter_out                   false
% 1.58/0.99  --pred_elim                             true
% 1.58/0.99  --res_sim_input                         true
% 1.58/0.99  --eq_ax_congr_red                       true
% 1.58/0.99  --pure_diseq_elim                       true
% 1.58/0.99  --brand_transform                       false
% 1.58/0.99  --non_eq_to_eq                          false
% 1.58/0.99  --prep_def_merge                        true
% 1.58/0.99  --prep_def_merge_prop_impl              false
% 1.58/0.99  --prep_def_merge_mbd                    true
% 1.58/0.99  --prep_def_merge_tr_red                 false
% 1.58/0.99  --prep_def_merge_tr_cl                  false
% 1.58/0.99  --smt_preprocessing                     true
% 1.58/0.99  --smt_ac_axioms                         fast
% 1.58/0.99  --preprocessed_out                      false
% 1.58/0.99  --preprocessed_stats                    false
% 1.58/0.99  
% 1.58/0.99  ------ Abstraction refinement Options
% 1.58/0.99  
% 1.58/0.99  --abstr_ref                             []
% 1.58/0.99  --abstr_ref_prep                        false
% 1.58/0.99  --abstr_ref_until_sat                   false
% 1.58/0.99  --abstr_ref_sig_restrict                funpre
% 1.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/0.99  --abstr_ref_under                       []
% 1.58/0.99  
% 1.58/0.99  ------ SAT Options
% 1.58/0.99  
% 1.58/0.99  --sat_mode                              false
% 1.58/0.99  --sat_fm_restart_options                ""
% 1.58/0.99  --sat_gr_def                            false
% 1.58/0.99  --sat_epr_types                         true
% 1.58/0.99  --sat_non_cyclic_types                  false
% 1.58/0.99  --sat_finite_models                     false
% 1.58/0.99  --sat_fm_lemmas                         false
% 1.58/0.99  --sat_fm_prep                           false
% 1.58/0.99  --sat_fm_uc_incr                        true
% 1.58/0.99  --sat_out_model                         small
% 1.58/0.99  --sat_out_clauses                       false
% 1.58/0.99  
% 1.58/0.99  ------ QBF Options
% 1.58/0.99  
% 1.58/0.99  --qbf_mode                              false
% 1.58/0.99  --qbf_elim_univ                         false
% 1.58/0.99  --qbf_dom_inst                          none
% 1.58/0.99  --qbf_dom_pre_inst                      false
% 1.58/0.99  --qbf_sk_in                             false
% 1.58/0.99  --qbf_pred_elim                         true
% 1.58/0.99  --qbf_split                             512
% 1.58/0.99  
% 1.58/0.99  ------ BMC1 Options
% 1.58/0.99  
% 1.58/0.99  --bmc1_incremental                      false
% 1.58/0.99  --bmc1_axioms                           reachable_all
% 1.58/0.99  --bmc1_min_bound                        0
% 1.58/0.99  --bmc1_max_bound                        -1
% 1.58/0.99  --bmc1_max_bound_default                -1
% 1.58/0.99  --bmc1_symbol_reachability              true
% 1.58/0.99  --bmc1_property_lemmas                  false
% 1.58/0.99  --bmc1_k_induction                      false
% 1.58/0.99  --bmc1_non_equiv_states                 false
% 1.58/0.99  --bmc1_deadlock                         false
% 1.58/0.99  --bmc1_ucm                              false
% 1.58/0.99  --bmc1_add_unsat_core                   none
% 1.58/0.99  --bmc1_unsat_core_children              false
% 1.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/0.99  --bmc1_out_stat                         full
% 1.58/0.99  --bmc1_ground_init                      false
% 1.58/0.99  --bmc1_pre_inst_next_state              false
% 1.58/0.99  --bmc1_pre_inst_state                   false
% 1.58/0.99  --bmc1_pre_inst_reach_state             false
% 1.58/0.99  --bmc1_out_unsat_core                   false
% 1.58/0.99  --bmc1_aig_witness_out                  false
% 1.58/0.99  --bmc1_verbose                          false
% 1.58/0.99  --bmc1_dump_clauses_tptp                false
% 1.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.58/0.99  --bmc1_dump_file                        -
% 1.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.58/0.99  --bmc1_ucm_extend_mode                  1
% 1.58/0.99  --bmc1_ucm_init_mode                    2
% 1.58/0.99  --bmc1_ucm_cone_mode                    none
% 1.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.58/0.99  --bmc1_ucm_relax_model                  4
% 1.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/0.99  --bmc1_ucm_layered_model                none
% 1.58/0.99  --bmc1_ucm_max_lemma_size               10
% 1.58/0.99  
% 1.58/0.99  ------ AIG Options
% 1.58/0.99  
% 1.58/0.99  --aig_mode                              false
% 1.58/0.99  
% 1.58/0.99  ------ Instantiation Options
% 1.58/0.99  
% 1.58/0.99  --instantiation_flag                    true
% 1.58/0.99  --inst_sos_flag                         false
% 1.58/0.99  --inst_sos_phase                        true
% 1.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/0.99  --inst_lit_sel_side                     num_symb
% 1.58/0.99  --inst_solver_per_active                1400
% 1.58/0.99  --inst_solver_calls_frac                1.
% 1.58/0.99  --inst_passive_queue_type               priority_queues
% 1.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/0.99  --inst_passive_queues_freq              [25;2]
% 1.58/0.99  --inst_dismatching                      true
% 1.58/0.99  --inst_eager_unprocessed_to_passive     true
% 1.58/0.99  --inst_prop_sim_given                   true
% 1.58/0.99  --inst_prop_sim_new                     false
% 1.58/0.99  --inst_subs_new                         false
% 1.58/0.99  --inst_eq_res_simp                      false
% 1.58/0.99  --inst_subs_given                       false
% 1.58/0.99  --inst_orphan_elimination               true
% 1.58/0.99  --inst_learning_loop_flag               true
% 1.58/0.99  --inst_learning_start                   3000
% 1.58/0.99  --inst_learning_factor                  2
% 1.58/0.99  --inst_start_prop_sim_after_learn       3
% 1.58/0.99  --inst_sel_renew                        solver
% 1.58/0.99  --inst_lit_activity_flag                true
% 1.58/0.99  --inst_restr_to_given                   false
% 1.58/0.99  --inst_activity_threshold               500
% 1.58/0.99  --inst_out_proof                        true
% 1.58/0.99  
% 1.58/0.99  ------ Resolution Options
% 1.58/0.99  
% 1.58/0.99  --resolution_flag                       true
% 1.58/0.99  --res_lit_sel                           adaptive
% 1.58/0.99  --res_lit_sel_side                      none
% 1.58/0.99  --res_ordering                          kbo
% 1.58/0.99  --res_to_prop_solver                    active
% 1.58/0.99  --res_prop_simpl_new                    false
% 1.58/0.99  --res_prop_simpl_given                  true
% 1.58/0.99  --res_passive_queue_type                priority_queues
% 1.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/0.99  --res_passive_queues_freq               [15;5]
% 1.58/0.99  --res_forward_subs                      full
% 1.58/0.99  --res_backward_subs                     full
% 1.58/0.99  --res_forward_subs_resolution           true
% 1.58/0.99  --res_backward_subs_resolution          true
% 1.58/0.99  --res_orphan_elimination                true
% 1.58/0.99  --res_time_limit                        2.
% 1.58/0.99  --res_out_proof                         true
% 1.58/0.99  
% 1.58/0.99  ------ Superposition Options
% 1.58/0.99  
% 1.58/0.99  --superposition_flag                    true
% 1.58/0.99  --sup_passive_queue_type                priority_queues
% 1.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.58/0.99  --demod_completeness_check              fast
% 1.58/0.99  --demod_use_ground                      true
% 1.58/0.99  --sup_to_prop_solver                    passive
% 1.58/0.99  --sup_prop_simpl_new                    true
% 1.58/0.99  --sup_prop_simpl_given                  true
% 1.58/0.99  --sup_fun_splitting                     false
% 1.58/0.99  --sup_smt_interval                      50000
% 1.58/0.99  
% 1.58/0.99  ------ Superposition Simplification Setup
% 1.58/0.99  
% 1.58/0.99  --sup_indices_passive                   []
% 1.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_full_bw                           [BwDemod]
% 1.58/0.99  --sup_immed_triv                        [TrivRules]
% 1.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_immed_bw_main                     []
% 1.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.99  
% 1.58/0.99  ------ Combination Options
% 1.58/0.99  
% 1.58/0.99  --comb_res_mult                         3
% 1.58/0.99  --comb_sup_mult                         2
% 1.58/0.99  --comb_inst_mult                        10
% 1.58/0.99  
% 1.58/0.99  ------ Debug Options
% 1.58/0.99  
% 1.58/0.99  --dbg_backtrace                         false
% 1.58/0.99  --dbg_dump_prop_clauses                 false
% 1.58/0.99  --dbg_dump_prop_clauses_file            -
% 1.58/0.99  --dbg_out_stat                          false
% 1.58/0.99  ------ Parsing...
% 1.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.58/0.99  ------ Proving...
% 1.58/0.99  ------ Problem Properties 
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  clauses                                 10
% 1.58/0.99  conjectures                             0
% 1.58/0.99  EPR                                     0
% 1.58/0.99  Horn                                    10
% 1.58/0.99  unary                                   3
% 1.58/0.99  binary                                  5
% 1.58/0.99  lits                                    19
% 1.58/0.99  lits eq                                 19
% 1.58/0.99  fd_pure                                 0
% 1.58/0.99  fd_pseudo                               0
% 1.58/0.99  fd_cond                                 0
% 1.58/0.99  fd_pseudo_cond                          0
% 1.58/0.99  AC symbols                              0
% 1.58/0.99  
% 1.58/0.99  ------ Schedule dynamic 5 is on 
% 1.58/0.99  
% 1.58/0.99  ------ no conjectures: strip conj schedule 
% 1.58/0.99  
% 1.58/0.99  ------ pure equality problem: resolution off 
% 1.58/0.99  
% 1.58/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  ------ 
% 1.58/0.99  Current options:
% 1.58/0.99  ------ 
% 1.58/0.99  
% 1.58/0.99  ------ Input Options
% 1.58/0.99  
% 1.58/0.99  --out_options                           all
% 1.58/0.99  --tptp_safe_out                         true
% 1.58/0.99  --problem_path                          ""
% 1.58/0.99  --include_path                          ""
% 1.58/0.99  --clausifier                            res/vclausify_rel
% 1.58/0.99  --clausifier_options                    --mode clausify
% 1.58/0.99  --stdin                                 false
% 1.58/0.99  --stats_out                             all
% 1.58/0.99  
% 1.58/0.99  ------ General Options
% 1.58/0.99  
% 1.58/0.99  --fof                                   false
% 1.58/0.99  --time_out_real                         305.
% 1.58/0.99  --time_out_virtual                      -1.
% 1.58/0.99  --symbol_type_check                     false
% 1.58/0.99  --clausify_out                          false
% 1.58/0.99  --sig_cnt_out                           false
% 1.58/0.99  --trig_cnt_out                          false
% 1.58/0.99  --trig_cnt_out_tolerance                1.
% 1.58/0.99  --trig_cnt_out_sk_spl                   false
% 1.58/0.99  --abstr_cl_out                          false
% 1.58/0.99  
% 1.58/0.99  ------ Global Options
% 1.58/0.99  
% 1.58/0.99  --schedule                              default
% 1.58/0.99  --add_important_lit                     false
% 1.58/0.99  --prop_solver_per_cl                    1000
% 1.58/0.99  --min_unsat_core                        false
% 1.58/0.99  --soft_assumptions                      false
% 1.58/0.99  --soft_lemma_size                       3
% 1.58/0.99  --prop_impl_unit_size                   0
% 1.58/0.99  --prop_impl_unit                        []
% 1.58/0.99  --share_sel_clauses                     true
% 1.58/0.99  --reset_solvers                         false
% 1.58/0.99  --bc_imp_inh                            [conj_cone]
% 1.58/0.99  --conj_cone_tolerance                   3.
% 1.58/0.99  --extra_neg_conj                        none
% 1.58/0.99  --large_theory_mode                     true
% 1.58/0.99  --prolific_symb_bound                   200
% 1.58/0.99  --lt_threshold                          2000
% 1.58/0.99  --clause_weak_htbl                      true
% 1.58/0.99  --gc_record_bc_elim                     false
% 1.58/0.99  
% 1.58/0.99  ------ Preprocessing Options
% 1.58/0.99  
% 1.58/0.99  --preprocessing_flag                    true
% 1.58/0.99  --time_out_prep_mult                    0.1
% 1.58/0.99  --splitting_mode                        input
% 1.58/0.99  --splitting_grd                         true
% 1.58/0.99  --splitting_cvd                         false
% 1.58/0.99  --splitting_cvd_svl                     false
% 1.58/0.99  --splitting_nvd                         32
% 1.58/0.99  --sub_typing                            true
% 1.58/0.99  --prep_gs_sim                           true
% 1.58/0.99  --prep_unflatten                        true
% 1.58/0.99  --prep_res_sim                          true
% 1.58/0.99  --prep_upred                            true
% 1.58/0.99  --prep_sem_filter                       exhaustive
% 1.58/0.99  --prep_sem_filter_out                   false
% 1.58/0.99  --pred_elim                             true
% 1.58/0.99  --res_sim_input                         true
% 1.58/0.99  --eq_ax_congr_red                       true
% 1.58/0.99  --pure_diseq_elim                       true
% 1.58/0.99  --brand_transform                       false
% 1.58/0.99  --non_eq_to_eq                          false
% 1.58/0.99  --prep_def_merge                        true
% 1.58/0.99  --prep_def_merge_prop_impl              false
% 1.58/0.99  --prep_def_merge_mbd                    true
% 1.58/0.99  --prep_def_merge_tr_red                 false
% 1.58/0.99  --prep_def_merge_tr_cl                  false
% 1.58/0.99  --smt_preprocessing                     true
% 1.58/0.99  --smt_ac_axioms                         fast
% 1.58/0.99  --preprocessed_out                      false
% 1.58/0.99  --preprocessed_stats                    false
% 1.58/0.99  
% 1.58/0.99  ------ Abstraction refinement Options
% 1.58/0.99  
% 1.58/0.99  --abstr_ref                             []
% 1.58/0.99  --abstr_ref_prep                        false
% 1.58/0.99  --abstr_ref_until_sat                   false
% 1.58/0.99  --abstr_ref_sig_restrict                funpre
% 1.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/0.99  --abstr_ref_under                       []
% 1.58/0.99  
% 1.58/0.99  ------ SAT Options
% 1.58/0.99  
% 1.58/0.99  --sat_mode                              false
% 1.58/0.99  --sat_fm_restart_options                ""
% 1.58/0.99  --sat_gr_def                            false
% 1.58/0.99  --sat_epr_types                         true
% 1.58/0.99  --sat_non_cyclic_types                  false
% 1.58/0.99  --sat_finite_models                     false
% 1.58/0.99  --sat_fm_lemmas                         false
% 1.58/0.99  --sat_fm_prep                           false
% 1.58/0.99  --sat_fm_uc_incr                        true
% 1.58/0.99  --sat_out_model                         small
% 1.58/0.99  --sat_out_clauses                       false
% 1.58/0.99  
% 1.58/0.99  ------ QBF Options
% 1.58/0.99  
% 1.58/0.99  --qbf_mode                              false
% 1.58/0.99  --qbf_elim_univ                         false
% 1.58/0.99  --qbf_dom_inst                          none
% 1.58/0.99  --qbf_dom_pre_inst                      false
% 1.58/0.99  --qbf_sk_in                             false
% 1.58/0.99  --qbf_pred_elim                         true
% 1.58/0.99  --qbf_split                             512
% 1.58/0.99  
% 1.58/0.99  ------ BMC1 Options
% 1.58/0.99  
% 1.58/0.99  --bmc1_incremental                      false
% 1.58/0.99  --bmc1_axioms                           reachable_all
% 1.58/0.99  --bmc1_min_bound                        0
% 1.58/0.99  --bmc1_max_bound                        -1
% 1.58/0.99  --bmc1_max_bound_default                -1
% 1.58/0.99  --bmc1_symbol_reachability              true
% 1.58/0.99  --bmc1_property_lemmas                  false
% 1.58/0.99  --bmc1_k_induction                      false
% 1.58/0.99  --bmc1_non_equiv_states                 false
% 1.58/0.99  --bmc1_deadlock                         false
% 1.58/0.99  --bmc1_ucm                              false
% 1.58/0.99  --bmc1_add_unsat_core                   none
% 1.58/0.99  --bmc1_unsat_core_children              false
% 1.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/0.99  --bmc1_out_stat                         full
% 1.58/0.99  --bmc1_ground_init                      false
% 1.58/0.99  --bmc1_pre_inst_next_state              false
% 1.58/0.99  --bmc1_pre_inst_state                   false
% 1.58/0.99  --bmc1_pre_inst_reach_state             false
% 1.58/0.99  --bmc1_out_unsat_core                   false
% 1.58/0.99  --bmc1_aig_witness_out                  false
% 1.58/0.99  --bmc1_verbose                          false
% 1.58/0.99  --bmc1_dump_clauses_tptp                false
% 1.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.58/0.99  --bmc1_dump_file                        -
% 1.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.58/0.99  --bmc1_ucm_extend_mode                  1
% 1.58/0.99  --bmc1_ucm_init_mode                    2
% 1.58/0.99  --bmc1_ucm_cone_mode                    none
% 1.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.58/0.99  --bmc1_ucm_relax_model                  4
% 1.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/0.99  --bmc1_ucm_layered_model                none
% 1.58/0.99  --bmc1_ucm_max_lemma_size               10
% 1.58/0.99  
% 1.58/0.99  ------ AIG Options
% 1.58/0.99  
% 1.58/0.99  --aig_mode                              false
% 1.58/0.99  
% 1.58/0.99  ------ Instantiation Options
% 1.58/0.99  
% 1.58/0.99  --instantiation_flag                    true
% 1.58/0.99  --inst_sos_flag                         false
% 1.58/0.99  --inst_sos_phase                        true
% 1.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/0.99  --inst_lit_sel_side                     none
% 1.58/0.99  --inst_solver_per_active                1400
% 1.58/0.99  --inst_solver_calls_frac                1.
% 1.58/0.99  --inst_passive_queue_type               priority_queues
% 1.58/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.58/0.99  --inst_passive_queues_freq              [25;2]
% 1.58/0.99  --inst_dismatching                      true
% 1.58/0.99  --inst_eager_unprocessed_to_passive     true
% 1.58/0.99  --inst_prop_sim_given                   true
% 1.58/0.99  --inst_prop_sim_new                     false
% 1.58/0.99  --inst_subs_new                         false
% 1.58/0.99  --inst_eq_res_simp                      false
% 1.58/0.99  --inst_subs_given                       false
% 1.58/0.99  --inst_orphan_elimination               true
% 1.58/0.99  --inst_learning_loop_flag               true
% 1.58/0.99  --inst_learning_start                   3000
% 1.58/0.99  --inst_learning_factor                  2
% 1.58/0.99  --inst_start_prop_sim_after_learn       3
% 1.58/0.99  --inst_sel_renew                        solver
% 1.58/0.99  --inst_lit_activity_flag                true
% 1.58/0.99  --inst_restr_to_given                   false
% 1.58/0.99  --inst_activity_threshold               500
% 1.58/0.99  --inst_out_proof                        true
% 1.58/0.99  
% 1.58/0.99  ------ Resolution Options
% 1.58/0.99  
% 1.58/0.99  --resolution_flag                       false
% 1.58/0.99  --res_lit_sel                           adaptive
% 1.58/0.99  --res_lit_sel_side                      none
% 1.58/0.99  --res_ordering                          kbo
% 1.58/0.99  --res_to_prop_solver                    active
% 1.58/0.99  --res_prop_simpl_new                    false
% 1.58/0.99  --res_prop_simpl_given                  true
% 1.58/0.99  --res_passive_queue_type                priority_queues
% 1.58/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.58/0.99  --res_passive_queues_freq               [15;5]
% 1.58/0.99  --res_forward_subs                      full
% 1.58/0.99  --res_backward_subs                     full
% 1.58/0.99  --res_forward_subs_resolution           true
% 1.58/0.99  --res_backward_subs_resolution          true
% 1.58/0.99  --res_orphan_elimination                true
% 1.58/0.99  --res_time_limit                        2.
% 1.58/0.99  --res_out_proof                         true
% 1.58/0.99  
% 1.58/0.99  ------ Superposition Options
% 1.58/0.99  
% 1.58/0.99  --superposition_flag                    true
% 1.58/0.99  --sup_passive_queue_type                priority_queues
% 1.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.58/0.99  --demod_completeness_check              fast
% 1.58/0.99  --demod_use_ground                      true
% 1.58/0.99  --sup_to_prop_solver                    passive
% 1.58/0.99  --sup_prop_simpl_new                    true
% 1.58/0.99  --sup_prop_simpl_given                  true
% 1.58/0.99  --sup_fun_splitting                     false
% 1.58/0.99  --sup_smt_interval                      50000
% 1.58/0.99  
% 1.58/0.99  ------ Superposition Simplification Setup
% 1.58/0.99  
% 1.58/0.99  --sup_indices_passive                   []
% 1.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_full_bw                           [BwDemod]
% 1.58/0.99  --sup_immed_triv                        [TrivRules]
% 1.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_immed_bw_main                     []
% 1.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.99  
% 1.58/0.99  ------ Combination Options
% 1.58/0.99  
% 1.58/0.99  --comb_res_mult                         3
% 1.58/0.99  --comb_sup_mult                         2
% 1.58/0.99  --comb_inst_mult                        10
% 1.58/0.99  
% 1.58/0.99  ------ Debug Options
% 1.58/0.99  
% 1.58/0.99  --dbg_backtrace                         false
% 1.58/0.99  --dbg_dump_prop_clauses                 false
% 1.58/0.99  --dbg_dump_prop_clauses_file            -
% 1.58/0.99  --dbg_out_stat                          false
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  ------ Proving...
% 1.58/0.99  
% 1.58/0.99  
% 1.58/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.58/0.99  
% 1.58/0.99  % SZS output start Saturation for theBenchmark.p
% 1.58/0.99  
% 1.58/0.99  fof(f13,conjecture,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f14,negated_conjecture,(
% 1.58/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.58/0.99    inference(negated_conjecture,[],[f13])).
% 1.58/0.99  
% 1.58/0.99  fof(f38,plain,(
% 1.58/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f14])).
% 1.58/0.99  
% 1.58/0.99  fof(f39,plain,(
% 1.58/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f38])).
% 1.58/0.99  
% 1.58/0.99  fof(f47,plain,(
% 1.58/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK3) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 1.58/0.99    introduced(choice_axiom,[])).
% 1.58/0.99  
% 1.58/0.99  fof(f46,plain,(
% 1.58/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.58/0.99    introduced(choice_axiom,[])).
% 1.58/0.99  
% 1.58/0.99  fof(f45,plain,(
% 1.58/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.58/0.99    introduced(choice_axiom,[])).
% 1.58/0.99  
% 1.58/0.99  fof(f48,plain,(
% 1.58/0.99    ((~r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f47,f46,f45])).
% 1.58/0.99  
% 1.58/0.99  fof(f76,plain,(
% 1.58/0.99    m1_pre_topc(sK2,sK1)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f10,axiom,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f33,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f10])).
% 1.58/0.99  
% 1.58/0.99  fof(f34,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f33])).
% 1.58/0.99  
% 1.58/0.99  fof(f69,plain,(
% 1.58/0.99    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f34])).
% 1.58/0.99  
% 1.58/0.99  fof(f82,plain,(
% 1.58/0.99    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(equality_resolution,[],[f69])).
% 1.58/0.99  
% 1.58/0.99  fof(f12,axiom,(
% 1.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f37,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/0.99    inference(ennf_transformation,[],[f12])).
% 1.58/0.99  
% 1.58/0.99  fof(f71,plain,(
% 1.58/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f37])).
% 1.58/0.99  
% 1.58/0.99  fof(f78,plain,(
% 1.58/0.99    ~r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f75,plain,(
% 1.58/0.99    ~v2_struct_0(sK2)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f77,plain,(
% 1.58/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f72,plain,(
% 1.58/0.99    ~v2_struct_0(sK1)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f73,plain,(
% 1.58/0.99    v2_pre_topc(sK1)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f74,plain,(
% 1.58/0.99    l1_pre_topc(sK1)),
% 1.58/0.99    inference(cnf_transformation,[],[f48])).
% 1.58/0.99  
% 1.58/0.99  fof(f5,axiom,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f23,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f5])).
% 1.58/0.99  
% 1.58/0.99  fof(f24,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f23])).
% 1.58/0.99  
% 1.58/0.99  fof(f41,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(nnf_transformation,[],[f24])).
% 1.58/0.99  
% 1.58/0.99  fof(f42,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(rectify,[],[f41])).
% 1.58/0.99  
% 1.58/0.99  fof(f43,plain,(
% 1.58/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/0.99    introduced(choice_axiom,[])).
% 1.58/0.99  
% 1.58/0.99  fof(f44,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 1.58/0.99  
% 1.58/0.99  fof(f54,plain,(
% 1.58/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f44])).
% 1.58/0.99  
% 1.58/0.99  fof(f80,plain,(
% 1.58/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(equality_resolution,[],[f54])).
% 1.58/0.99  
% 1.58/0.99  fof(f81,plain,(
% 1.58/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(equality_resolution,[],[f80])).
% 1.58/0.99  
% 1.58/0.99  fof(f9,axiom,(
% 1.58/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f31,plain,(
% 1.58/0.99    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f9])).
% 1.58/0.99  
% 1.58/0.99  fof(f32,plain,(
% 1.58/0.99    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f31])).
% 1.58/0.99  
% 1.58/0.99  fof(f67,plain,(
% 1.58/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f32])).
% 1.58/0.99  
% 1.58/0.99  fof(f68,plain,(
% 1.58/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f32])).
% 1.58/0.99  
% 1.58/0.99  fof(f6,axiom,(
% 1.58/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f25,plain,(
% 1.58/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f6])).
% 1.58/0.99  
% 1.58/0.99  fof(f26,plain,(
% 1.58/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f25])).
% 1.58/0.99  
% 1.58/0.99  fof(f60,plain,(
% 1.58/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f26])).
% 1.58/0.99  
% 1.58/0.99  fof(f4,axiom,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f21,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f4])).
% 1.58/0.99  
% 1.58/0.99  fof(f22,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f21])).
% 1.58/0.99  
% 1.58/0.99  fof(f53,plain,(
% 1.58/0.99    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f22])).
% 1.58/0.99  
% 1.58/0.99  fof(f1,axiom,(
% 1.58/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f16,plain,(
% 1.58/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.58/0.99    inference(ennf_transformation,[],[f1])).
% 1.58/0.99  
% 1.58/0.99  fof(f49,plain,(
% 1.58/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f16])).
% 1.58/0.99  
% 1.58/0.99  fof(f2,axiom,(
% 1.58/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f17,plain,(
% 1.58/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f2])).
% 1.58/0.99  
% 1.58/0.99  fof(f18,plain,(
% 1.58/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f17])).
% 1.58/0.99  
% 1.58/0.99  fof(f50,plain,(
% 1.58/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f18])).
% 1.58/0.99  
% 1.58/0.99  fof(f3,axiom,(
% 1.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f19,plain,(
% 1.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.58/0.99    inference(ennf_transformation,[],[f3])).
% 1.58/0.99  
% 1.58/0.99  fof(f20,plain,(
% 1.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.58/0.99    inference(flattening,[],[f19])).
% 1.58/0.99  
% 1.58/0.99  fof(f40,plain,(
% 1.58/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.58/0.99    inference(nnf_transformation,[],[f20])).
% 1.58/0.99  
% 1.58/0.99  fof(f51,plain,(
% 1.58/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f40])).
% 1.58/0.99  
% 1.58/0.99  fof(f11,axiom,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f35,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f11])).
% 1.58/0.99  
% 1.58/0.99  fof(f36,plain,(
% 1.58/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f35])).
% 1.58/0.99  
% 1.58/0.99  fof(f70,plain,(
% 1.58/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f36])).
% 1.58/0.99  
% 1.58/0.99  fof(f8,axiom,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k3_struct_0(X0),X0,X0) & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k3_struct_0(X0))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f15,plain,(
% 1.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k3_struct_0(X0))))),
% 1.58/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.58/0.99  
% 1.58/0.99  fof(f29,plain,(
% 1.58/0.99    ! [X0] : ((v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k3_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f15])).
% 1.58/0.99  
% 1.58/0.99  fof(f30,plain,(
% 1.58/0.99    ! [X0] : ((v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k3_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f29])).
% 1.58/0.99  
% 1.58/0.99  fof(f64,plain,(
% 1.58/0.99    ( ! [X0] : (v1_funct_1(k3_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f30])).
% 1.58/0.99  
% 1.58/0.99  fof(f65,plain,(
% 1.58/0.99    ( ! [X0] : (v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f30])).
% 1.58/0.99  
% 1.58/0.99  fof(f7,axiom,(
% 1.58/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 1.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.99  
% 1.58/0.99  fof(f27,plain,(
% 1.58/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.99    inference(ennf_transformation,[],[f7])).
% 1.58/0.99  
% 1.58/0.99  fof(f28,plain,(
% 1.58/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.99    inference(flattening,[],[f27])).
% 1.58/0.99  
% 1.58/0.99  fof(f62,plain,(
% 1.58/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f28])).
% 1.58/0.99  
% 1.58/0.99  fof(f61,plain,(
% 1.58/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f28])).
% 1.58/0.99  
% 1.58/0.99  fof(f63,plain,(
% 1.58/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f28])).
% 1.58/0.99  
% 1.58/0.99  fof(f66,plain,(
% 1.58/0.99    ( ! [X0,X1] : (~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f32])).
% 1.58/0.99  
% 1.58/0.99  fof(f59,plain,(
% 1.58/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.99    inference(cnf_transformation,[],[f26])).
% 1.58/0.99  
% 1.58/0.99  cnf(c_311,plain,
% 1.58/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.58/0.99      | r1_tmap_1(X4,X5,X6,X7)
% 1.58/0.99      | X6 != X2
% 1.58/0.99      | X4 != X0
% 1.58/0.99      | X5 != X1
% 1.58/0.99      | X7 != X3 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_308,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_307,plain,
% 1.58/0.99      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_304,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_301,plain,
% 1.58/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_300,plain,
% 1.58/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.58/0.99      | v1_funct_2(X3,X4,X5)
% 1.58/0.99      | X5 != X2
% 1.58/0.99      | X3 != X0
% 1.58/0.99      | X4 != X1 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_299,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_296,plain,
% 1.58/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.58/0.99      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 1.58/0.99      | X8 != X2
% 1.58/0.99      | X6 != X0
% 1.58/0.99      | X7 != X1
% 1.58/0.99      | X9 != X3
% 1.58/0.99      | X10 != X4
% 1.58/0.99      | X11 != X5 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_295,plain,
% 1.58/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_294,plain,
% 1.58/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_292,plain,
% 1.58/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 1.58/0.99      theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_289,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_25,negated_conjecture,
% 1.58/0.99      ( m1_pre_topc(sK2,sK1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_20,plain,
% 1.58/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.58/0.99      | ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.58/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_22,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_172,plain,
% 1.58/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.58/0.99      | ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_20,c_22]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_173,plain,
% 1.58/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.58/0.99      | ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_172]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_23,negated_conjecture,
% 1.58/0.99      ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
% 1.58/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_358,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
% 1.58/0.99      | sK3 != X2
% 1.58/0.99      | sK2 != X0 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_173,c_23]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_359,plain,
% 1.58/0.99      ( ~ m1_pre_topc(sK2,X0)
% 1.58/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(sK2)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_26,negated_conjecture,
% 1.58/0.99      ( ~ v2_struct_0(sK2) ),
% 1.58/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_24,negated_conjecture,
% 1.58/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.58/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_363,plain,
% 1.58/0.99      ( v2_struct_0(X0)
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | ~ m1_pre_topc(sK2,X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_359,c_26,c_24]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_364,plain,
% 1.58/0.99      ( ~ m1_pre_topc(sK2,X0)
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_363]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_824,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != sK2 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_364]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_825,plain,
% 1.58/0.99      ( ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1)
% 1.58/0.99      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_824]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_29,negated_conjecture,
% 1.58/0.99      ( ~ v2_struct_0(sK1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_28,negated_conjecture,
% 1.58/0.99      ( v2_pre_topc(sK1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_27,negated_conjecture,
% 1.58/0.99      ( l1_pre_topc(sK1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_366,plain,
% 1.58/0.99      ( ~ m1_pre_topc(sK2,sK1)
% 1.58/0.99      | ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1)
% 1.58/0.99      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 1.58/0.99      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(instantiation,[status(thm)],[c_364]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_8,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_18,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_17,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_9,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 1.58/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_190,plain,
% 1.58/0.99      ( ~ l1_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_8,c_22,c_18,c_17,c_9]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_191,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_190]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_669,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_191,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_670,plain,
% 1.58/0.99      ( ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1)
% 1.58/0.99      | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_669]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_827,plain,
% 1.58/0.99      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_825,c_29,c_28,c_27,c_25,c_366,c_670]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1079,plain,
% 1.58/0.99      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 1.58/0.99      inference(subtyping,[status(esa)],[c_827]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_677,plain,
% 1.58/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | sK1 != X1
% 1.58/0.99      | sK2 != X0 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_678,plain,
% 1.58/0.99      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/0.99      | ~ l1_pre_topc(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_677]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_680,plain,
% 1.58/0.99      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_678,c_27]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_4,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 1.58/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_900,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 1.58/0.99      | sK1 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_901,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1)
% 1.58/0.99      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_900]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_905,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/0.99      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_901,c_29,c_27]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1013,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
% 1.58/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.58/0.99      | u1_struct_0(sK2) != X0 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_680,c_905]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1014,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_1013]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1074,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
% 1.58/0.99      inference(subtyping,[status(esa)],[c_1014]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_672,plain,
% 1.58/0.99      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_670,c_29,c_28,c_27]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1080,plain,
% 1.58/0.99      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 1.58/0.99      inference(subtyping,[status(esa)],[c_672]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1122,plain,
% 1.58/0.99      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 1.58/0.99      inference(light_normalisation,[status(thm)],[c_1079,c_1074,c_1080]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_0,plain,
% 1.58/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1,plain,
% 1.58/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_340,plain,
% 1.58/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 1.58/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_3,plain,
% 1.58/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.58/0.99      | ~ v1_funct_2(X5,X2,X3)
% 1.58/0.99      | ~ v1_funct_2(X4,X0,X1)
% 1.58/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.58/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/0.99      | ~ v1_funct_1(X5)
% 1.58/0.99      | ~ v1_funct_1(X4)
% 1.58/0.99      | v1_xboole_0(X1)
% 1.58/0.99      | v1_xboole_0(X3)
% 1.58/0.99      | X4 = X5 ),
% 1.58/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_21,plain,
% 1.58/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 1.58/0.99      | ~ m1_pre_topc(X1,X0)
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_397,plain,
% 1.58/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.58/0.99      | ~ v1_funct_2(X3,X4,X5)
% 1.58/0.99      | ~ m1_pre_topc(X6,X7)
% 1.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.58/0.99      | ~ v2_pre_topc(X7)
% 1.58/0.99      | ~ v1_funct_1(X0)
% 1.58/0.99      | ~ v1_funct_1(X3)
% 1.58/0.99      | v2_struct_0(X7)
% 1.58/0.99      | v2_struct_0(X6)
% 1.58/0.99      | v1_xboole_0(X2)
% 1.58/0.99      | v1_xboole_0(X5)
% 1.58/0.99      | ~ l1_pre_topc(X7)
% 1.58/0.99      | X3 = X0
% 1.58/0.99      | k9_tmap_1(X7,X6) != X0
% 1.58/0.99      | k3_struct_0(X7) != X3
% 1.58/0.99      | u1_struct_0(X7) != X5
% 1.58/0.99      | u1_struct_0(X7) != X4
% 1.58/0.99      | u1_struct_0(X7) != X1
% 1.58/0.99      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_398,plain,
% 1.58/0.99      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.58/0.99      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.58/0.99      | ~ m1_pre_topc(X1,X0)
% 1.58/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.58/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(X0))
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_16,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v1_funct_1(k3_struct_0(X0))
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_15,plain,
% 1.58/0.99      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_13,plain,
% 1.58/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.58/0.99      | ~ m1_pre_topc(X1,X0)
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0) ),
% 1.58/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_402,plain,
% 1.58/0.99      ( v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ m1_pre_topc(X1,X0)
% 1.58/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_398,c_16,c_15,c_13,c_340]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_403,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | ~ v1_funct_1(k9_tmap_1(X1,X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_402]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_14,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_12,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_408,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X1)
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.58/0.99      | ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_403,c_14,c_12]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_409,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X0)))
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k3_struct_0(X1) = k9_tmap_1(X1,X0) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_408]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_652,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.58/0.99      | ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_409,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_653,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | v2_struct_0(sK2)
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/0.99      | ~ l1_pre_topc(sK1)
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_652]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_655,plain,
% 1.58/0.99      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/0.99      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_653,c_29,c_28,c_27,c_26]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_656,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 1.58/0.99      inference(renaming,[status(thm)],[c_655]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_868,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/0.99      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_340,c_656]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_732,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_733,plain,
% 1.58/0.99      ( ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | ~ l1_pre_topc(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_732]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_735,plain,
% 1.58/0.99      ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_733,c_29,c_28,c_27]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_959,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/0.99      | k8_tmap_1(sK1,sK2) != X0
% 1.58/0.99      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_868,c_735]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_960,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_959]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_19,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ v2_struct_0(k8_tmap_1(X1,X0))
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_688,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ v2_struct_0(k8_tmap_1(X0,X1))
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_689,plain,
% 1.58/0.99      ( ~ v2_pre_topc(sK1)
% 1.58/0.99      | ~ v2_struct_0(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_688]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_962,plain,
% 1.58/0.99      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.58/0.99      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_960,c_29,c_28,c_27,c_689]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_976,plain,
% 1.58/0.99      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/0.99      | k3_struct_0(sK1) != sK3
% 1.58/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != u1_struct_0(sK2) ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_962]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1078,plain,
% 1.58/0.99      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/0.99      | k3_struct_0(sK1) != sK3
% 1.58/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != u1_struct_0(sK2) ),
% 1.58/0.99      inference(subtyping,[status(esa)],[c_976]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_986,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
% 1.58/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2)
% 1.58/0.99      | sK3 != X0 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_905]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_987,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,sK3) = k6_partfun1(u1_struct_0(sK1))
% 1.58/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_986]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_1077,plain,
% 1.58/0.99      ( k7_tmap_1(sK1,sK3) = k6_partfun1(u1_struct_0(sK1))
% 1.58/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK2) ),
% 1.58/0.99      inference(subtyping,[status(esa)],[c_987]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_10,plain,
% 1.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.58/0.99      | ~ v2_pre_topc(X1)
% 1.58/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1) ),
% 1.58/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_721,plain,
% 1.58/0.99      ( ~ v2_pre_topc(X0)
% 1.58/0.99      | v2_pre_topc(k8_tmap_1(X0,X1))
% 1.58/0.99      | v2_struct_0(X0)
% 1.58/0.99      | ~ l1_pre_topc(X0)
% 1.58/0.99      | sK1 != X0
% 1.58/0.99      | sK2 != X1 ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_722,plain,
% 1.58/0.99      ( v2_pre_topc(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | ~ v2_pre_topc(sK1)
% 1.58/0.99      | v2_struct_0(sK1)
% 1.58/0.99      | ~ l1_pre_topc(sK1) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_721]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_724,plain,
% 1.58/0.99      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 1.58/0.99      inference(global_propositional_subsumption,
% 1.58/0.99                [status(thm)],
% 1.58/0.99                [c_722,c_29,c_28,c_27]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_918,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/0.99      | v2_struct_0(X1)
% 1.58/0.99      | ~ l1_pre_topc(X1)
% 1.58/0.99      | k8_tmap_1(sK1,sK2) != X1
% 1.58/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 1.58/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_724]) ).
% 1.58/0.99  
% 1.58/0.99  cnf(c_919,plain,
% 1.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 1.58/0.99      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 1.58/0.99      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 1.58/0.99      inference(unflattening,[status(thm)],[c_918]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_923,plain,
% 1.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 1.58/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_919,c_29,c_28,c_27,c_689,c_733]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_994,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2)
% 1.58/1.00      | sK3 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_923]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_995,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),sK3) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_994]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1076,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),sK3) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != u1_struct_0(sK2) ),
% 1.58/1.00      inference(subtyping,[status(esa)],[c_995]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1002,plain,
% 1.58/1.00      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/1.00      | k3_struct_0(sK1) != u1_struct_0(sK2)
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_962,c_680]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1075,plain,
% 1.58/1.00      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 1.58/1.00      | k3_struct_0(sK1) != u1_struct_0(sK2)
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(subtyping,[status(esa)],[c_1002]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1018,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.58/1.00      | u1_struct_0(sK2) != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_680,c_923]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1019,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_1018]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1073,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(subtyping,[status(esa)],[c_1019]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_699,plain,
% 1.58/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.58/1.00      | ~ v2_pre_topc(X0)
% 1.58/1.00      | v2_struct_0(X0)
% 1.58/1.00      | ~ l1_pre_topc(X0)
% 1.58/1.00      | sK1 != X0
% 1.58/1.00      | sK2 != X1 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_700,plain,
% 1.58/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 1.58/1.00      | ~ v2_pre_topc(sK1)
% 1.58/1.00      | v2_struct_0(sK1)
% 1.58/1.00      | ~ l1_pre_topc(sK1) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_699]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_702,plain,
% 1.58/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_700,c_29,c_28,c_27]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1026,plain,
% 1.58/1.00      ( k9_tmap_1(sK1,sK2) != X0
% 1.58/1.00      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_905]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1027,plain,
% 1.58/1.00      ( k7_tmap_1(sK1,k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(sK1))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_1026]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1072,plain,
% 1.58/1.00      ( k7_tmap_1(sK1,k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(sK1))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.58/1.00      inference(subtyping,[status(esa)],[c_1027]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1034,plain,
% 1.58/1.00      ( k9_tmap_1(sK1,sK2) != X0
% 1.58/1.00      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_923]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1035,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_1034]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1071,plain,
% 1.58/1.00      ( k7_tmap_1(k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2)) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 1.58/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))) != k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 1.58/1.00      inference(subtyping,[status(esa)],[c_1035]) ).
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  % SZS output end Saturation for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  ------                               Statistics
% 1.58/1.00  
% 1.58/1.00  ------ General
% 1.58/1.00  
% 1.58/1.00  abstr_ref_over_cycles:                  0
% 1.58/1.00  abstr_ref_under_cycles:                 0
% 1.58/1.00  gc_basic_clause_elim:                   0
% 1.58/1.00  forced_gc_time:                         0
% 1.58/1.00  parsing_time:                           0.015
% 1.58/1.00  unif_index_cands_time:                  0.
% 1.58/1.00  unif_index_add_time:                    0.
% 1.58/1.00  orderings_time:                         0.
% 1.58/1.00  out_proof_time:                         0.
% 1.58/1.00  total_time:                             0.093
% 1.58/1.00  num_of_symbols:                         63
% 1.58/1.00  num_of_terms:                           1807
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing
% 1.58/1.00  
% 1.58/1.00  num_of_splits:                          0
% 1.58/1.00  num_of_split_atoms:                     0
% 1.58/1.00  num_of_reused_defs:                     0
% 1.58/1.00  num_eq_ax_congr_red:                    7
% 1.58/1.00  num_of_sem_filtered_clauses:            0
% 1.58/1.00  num_of_subtypes:                        3
% 1.58/1.00  monotx_restored_types:                  0
% 1.58/1.00  sat_num_of_epr_types:                   0
% 1.58/1.00  sat_num_of_non_cyclic_types:            0
% 1.58/1.00  sat_guarded_non_collapsed_types:        0
% 1.58/1.00  num_pure_diseq_elim:                    0
% 1.58/1.00  simp_replaced_by:                       0
% 1.58/1.00  res_preprocessed:                       64
% 1.58/1.00  prep_upred:                             0
% 1.58/1.00  prep_unflattend:                        53
% 1.58/1.00  smt_new_axioms:                         0
% 1.58/1.00  pred_elim_cands:                        0
% 1.58/1.00  pred_elim:                              12
% 1.58/1.00  pred_elim_cl:                           18
% 1.58/1.00  pred_elim_cycles:                       15
% 1.58/1.00  merged_defs:                            0
% 1.58/1.00  merged_defs_ncl:                        0
% 1.58/1.00  bin_hyper_res:                          0
% 1.58/1.00  prep_cycles:                            3
% 1.58/1.00  pred_elim_time:                         0.017
% 1.58/1.00  splitting_time:                         0.
% 1.58/1.00  sem_filter_time:                        0.
% 1.58/1.00  monotx_time:                            0.
% 1.58/1.00  subtype_inf_time:                       0.
% 1.58/1.00  
% 1.58/1.00  ------ Problem properties
% 1.58/1.00  
% 1.58/1.00  clauses:                                10
% 1.58/1.00  conjectures:                            0
% 1.58/1.00  epr:                                    0
% 1.58/1.00  horn:                                   10
% 1.58/1.00  ground:                                 10
% 1.58/1.00  unary:                                  3
% 1.58/1.00  binary:                                 5
% 1.58/1.00  lits:                                   19
% 1.58/1.00  lits_eq:                                19
% 1.58/1.00  fd_pure:                                0
% 1.58/1.00  fd_pseudo:                              0
% 1.58/1.00  fd_cond:                                0
% 1.58/1.00  fd_pseudo_cond:                         0
% 1.58/1.00  ac_symbols:                             0
% 1.58/1.00  
% 1.58/1.00  ------ Propositional Solver
% 1.58/1.00  
% 1.58/1.00  prop_solver_calls:                      21
% 1.58/1.00  prop_fast_solver_calls:                 683
% 1.58/1.00  smt_solver_calls:                       0
% 1.58/1.00  smt_fast_solver_calls:                  0
% 1.58/1.00  prop_num_of_clauses:                    371
% 1.58/1.00  prop_preprocess_simplified:             1533
% 1.58/1.00  prop_fo_subsumed:                       55
% 1.58/1.00  prop_solver_time:                       0.
% 1.58/1.00  smt_solver_time:                        0.
% 1.58/1.00  smt_fast_solver_time:                   0.
% 1.58/1.00  prop_fast_solver_time:                  0.
% 1.58/1.00  prop_unsat_core_time:                   0.
% 1.58/1.00  
% 1.58/1.00  ------ QBF
% 1.58/1.00  
% 1.58/1.00  qbf_q_res:                              0
% 1.58/1.00  qbf_num_tautologies:                    0
% 1.58/1.00  qbf_prep_cycles:                        0
% 1.58/1.00  
% 1.58/1.00  ------ BMC1
% 1.58/1.00  
% 1.58/1.00  bmc1_current_bound:                     -1
% 1.58/1.00  bmc1_last_solved_bound:                 -1
% 1.58/1.00  bmc1_unsat_core_size:                   -1
% 1.58/1.00  bmc1_unsat_core_parents_size:           -1
% 1.58/1.00  bmc1_merge_next_fun:                    0
% 1.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation
% 1.58/1.00  
% 1.58/1.00  inst_num_of_clauses:                    80
% 1.58/1.00  inst_num_in_passive:                    23
% 1.58/1.00  inst_num_in_active:                     57
% 1.58/1.00  inst_num_in_unprocessed:                0
% 1.58/1.00  inst_num_of_loops:                      60
% 1.58/1.00  inst_num_of_learning_restarts:          0
% 1.58/1.00  inst_num_moves_active_passive:          1
% 1.58/1.00  inst_lit_activity:                      0
% 1.58/1.00  inst_lit_activity_moves:                0
% 1.58/1.00  inst_num_tautologies:                   0
% 1.58/1.00  inst_num_prop_implied:                  0
% 1.58/1.00  inst_num_existing_simplified:           0
% 1.58/1.00  inst_num_eq_res_simplified:             0
% 1.58/1.00  inst_num_child_elim:                    0
% 1.58/1.00  inst_num_of_dismatching_blockings:      3
% 1.58/1.00  inst_num_of_non_proper_insts:           50
% 1.58/1.00  inst_num_of_duplicates:                 0
% 1.58/1.00  inst_inst_num_from_inst_to_res:         0
% 1.58/1.00  inst_dismatching_checking_time:         0.
% 1.58/1.00  
% 1.58/1.00  ------ Resolution
% 1.58/1.00  
% 1.58/1.00  res_num_of_clauses:                     0
% 1.58/1.00  res_num_in_passive:                     0
% 1.58/1.00  res_num_in_active:                      0
% 1.58/1.00  res_num_of_loops:                       67
% 1.58/1.00  res_forward_subset_subsumed:            2
% 1.58/1.00  res_backward_subset_subsumed:           5
% 1.58/1.00  res_forward_subsumed:                   0
% 1.58/1.00  res_backward_subsumed:                  0
% 1.58/1.00  res_forward_subsumption_resolution:     6
% 1.58/1.00  res_backward_subsumption_resolution:    0
% 1.58/1.00  res_clause_to_clause_subsumption:       49
% 1.58/1.00  res_orphan_elimination:                 0
% 1.58/1.00  res_tautology_del:                      18
% 1.58/1.00  res_num_eq_res_simplified:              0
% 1.58/1.00  res_num_sel_changes:                    0
% 1.58/1.00  res_moves_from_active_to_pass:          0
% 1.58/1.00  
% 1.58/1.00  ------ Superposition
% 1.58/1.00  
% 1.58/1.00  sup_time_total:                         0.
% 1.58/1.00  sup_time_generating:                    0.
% 1.58/1.00  sup_time_sim_full:                      0.
% 1.58/1.00  sup_time_sim_immed:                     0.
% 1.58/1.00  
% 1.58/1.00  sup_num_of_clauses:                     10
% 1.58/1.00  sup_num_in_active:                      10
% 1.58/1.00  sup_num_in_passive:                     0
% 1.58/1.00  sup_num_of_loops:                       10
% 1.58/1.00  sup_fw_superposition:                   0
% 1.58/1.00  sup_bw_superposition:                   0
% 1.58/1.00  sup_immediate_simplified:               0
% 1.58/1.00  sup_given_eliminated:                   0
% 1.58/1.00  comparisons_done:                       0
% 1.58/1.00  comparisons_avoided:                    0
% 1.58/1.00  
% 1.58/1.00  ------ Simplifications
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  sim_fw_subset_subsumed:                 0
% 1.58/1.00  sim_bw_subset_subsumed:                 0
% 1.58/1.00  sim_fw_subsumed:                        0
% 1.58/1.00  sim_bw_subsumed:                        0
% 1.58/1.00  sim_fw_subsumption_res:                 0
% 1.58/1.00  sim_bw_subsumption_res:                 0
% 1.58/1.00  sim_tautology_del:                      0
% 1.58/1.00  sim_eq_tautology_del:                   0
% 1.58/1.00  sim_eq_res_simp:                        0
% 1.58/1.00  sim_fw_demodulated:                     0
% 1.58/1.00  sim_bw_demodulated:                     0
% 1.58/1.00  sim_light_normalised:                   1
% 1.58/1.00  sim_joinable_taut:                      0
% 1.58/1.00  sim_joinable_simp:                      0
% 1.58/1.00  sim_ac_normalised:                      0
% 1.58/1.00  sim_smt_subsumption:                    0
% 1.58/1.00  
%------------------------------------------------------------------------------
